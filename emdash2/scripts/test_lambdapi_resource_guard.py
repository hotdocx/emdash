"""Focused safety checks; deliberately allocate only under small hard limits."""
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time
import unittest


GUARD = Path(__file__).with_name("lambdapi_resource_guard.sh")


class ResourceGuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="emdash-resource-test-")
        self.addCleanup(self.temp.cleanup)
        self.env = dict(os.environ, XDG_RUNTIME_DIR=self.temp.name,
                        EMDASH_LP_RESOURCE_BACKEND="prlimit",
                        EMDASH_LP_MEMORY_MIB="64", EMDASH_LP_FILE_MIB="1",
                        EMDASH_LP_TIMEOUT="5s")

    def run_guard(self, *args, **env):
        return subprocess.run(["bash", str(GUARD), *args],
                              env=dict(self.env, **env), capture_output=True,
                              text=True, timeout=10)

    def test_limits_inherited_by_child(self):
        result = self.run_guard("python3", "-c", """
import resource
assert resource.getrlimit(resource.RLIMIT_AS) == (64*1024**2,)*2
assert resource.getrlimit(resource.RLIMIT_FSIZE) == (1024**2,)*2
assert resource.getrlimit(resource.RLIMIT_CORE) == (0, 0)
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_oversized_mapping_is_refused(self):
        result = self.run_guard("python3", "-c", """
import mmap
try:
    mmap.mmap(-1, 128*1024**2)
except (OSError, MemoryError):
    pass
else:
    raise SystemExit('memory limit was not enforced')
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_file_growth_is_refused(self):
        target = str(Path(self.temp.name) / "bounded-output")
        result = self.run_guard("python3", "-c", """
import errno, signal, sys
signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
try:
    with open(sys.argv[1], 'wb', buffering=0) as stream:
        stream.write(b'x' * (2*1024**2))
        stream.write(b'x')
except OSError as error:
    assert error.errno == errno.EFBIG
else:
    raise SystemExit('file limit was not enforced')
""", target)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertLessEqual(Path(target).stat().st_size, 1024**2)

    def test_exit_status_is_preserved(self):
        result = self.run_guard("/bin/sh", "-c", "exit 7")
        self.assertEqual(result.returncode, 7)

    def test_wall_limit_is_hard(self):
        started = time.monotonic()
        result = self.run_guard("/bin/sleep", "20", EMDASH_LP_TIMEOUT="1s")
        self.assertIn(result.returncode, (-9, 137))
        self.assertLess(time.monotonic() - started, 5)

    def test_ceiling_cannot_be_raised_by_environment(self):
        for env in ({"EMDASH_LP_MEMORY_MIB": "6145"},
                    {"EMDASH_LP_TIMEOUT": "601s"},
                    {"EMDASH_LP_TIMEOUT": "180.5s"},
                    {"EMDASH_LP_TIMEOUT": "0"},
                    {"EMDASH_LP_FILE_MIB": "65"},
                    {"EMDASH_LP_MEMORY_MIB": "bad"}):
            with self.subTest(env=env):
                self.assertEqual(self.run_guard("/bin/true", **env).returncode, 2)

    def test_reviewed_memory_extension_keeps_other_limits(self):
        for memory in ("4096", "6144"):
            with self.subTest(memory=memory):
                result = self.run_guard("python3", "-c", """
import resource, sys
assert resource.getrlimit(resource.RLIMIT_AS) == (int(sys.argv[1])*1024**2,)*2
assert resource.getrlimit(resource.RLIMIT_FSIZE) == (1024**2,)*2
assert resource.getrlimit(resource.RLIMIT_CORE) == (0, 0)
""", memory, EMDASH_LP_MEMORY_MIB=memory)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_default_memory_remains_two_gib(self):
        env = dict(self.env)
        env.pop("EMDASH_LP_MEMORY_MIB")
        result = subprocess.run(["bash", str(GUARD), "python3", "-c", """
import resource
assert resource.getrlimit(resource.RLIMIT_AS) == (2048*1024**2,)*2
"""], env=env, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_reviewed_time_extension_keeps_other_limits(self):
        for duration in ("120", "180s", "240s", "300s", "450s", "600s"):
            with self.subTest(duration=duration):
                result = self.run_guard("python3", "-c", """
import resource
assert resource.getrlimit(resource.RLIMIT_AS) == (64*1024**2,)*2
assert resource.getrlimit(resource.RLIMIT_FSIZE) == (1024**2,)*2
assert resource.getrlimit(resource.RLIMIT_CORE) == (0, 0)
""", EMDASH_LP_TIMEOUT=duration)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("time=" + duration.removesuffix("s") + "s", result.stderr)

    def test_parallel_check_is_rejected(self):
        first = subprocess.Popen(
            ["bash", str(GUARD), "python3", "-c",
             "import time; print('ready', flush=True); time.sleep(2)"],
            env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True)
        try:
            self.assertEqual(first.stdout.readline().strip(), "ready")
            second = self.run_guard("/bin/true")
            self.assertEqual(second.returncode, 75, second.stderr)
            first.communicate(timeout=5)
            self.assertEqual(first.returncode, 0)
        finally:
            if first.poll() is None:
                first.kill()
                first.communicate()

    def test_systemd_group_limit_and_serialization(self):
        manager = subprocess.run(["systemctl", "--user", "is-active", "--quiet",
                                  "default.target"], capture_output=True)
        if manager.returncode:
            self.skipTest("no active user systemd manager")
        env = dict(os.environ, EMDASH_LP_RESOURCE_BACKEND="systemd",
                   EMDASH_LP_MEMORY_MIB="64", EMDASH_LP_FILE_MIB="1",
                   EMDASH_LP_TIMEOUT="5s")
        command = ('p=$(sed -n "s/^0:://p" /proc/self/cgroup); '
                   'cat "/sys/fs/cgroup$p/memory.max" '
                   '"/sys/fs/cgroup$p/memory.swap.max"; sleep 2')
        first = subprocess.Popen(["bash", str(GUARD), "/bin/sh", "-c", command],
                                 env=env, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True)
        try:
            self.assertEqual(first.stdout.readline().strip(), str(64*1024**2))
            self.assertEqual(first.stdout.readline().strip(), "0")
            second = subprocess.run(["bash", str(GUARD), "/bin/true"], env=env,
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(second.returncode, 75, second.stderr)
            first.communicate(timeout=5)
            self.assertEqual(first.returncode, 0)
        finally:
            if first.poll() is None:
                first.kill()
                first.communicate()
        failure = subprocess.run(["bash", str(GUARD), "/bin/sh", "-c", "exit 7"],
                                 env=env, capture_output=True, text=True, timeout=5)
        self.assertEqual(failure.returncode, 7, failure.stderr)

    def test_systemd_deadline_covers_detached_descendant(self):
        manager = subprocess.run(["systemctl", "--user", "is-active", "--quiet",
                                  "default.target"], capture_output=True)
        if manager.returncode:
            self.skipTest("no active user systemd manager")
        env = dict(os.environ, EMDASH_LP_RESOURCE_BACKEND="systemd",
                   EMDASH_LP_MEMORY_MIB="64", EMDASH_LP_FILE_MIB="1",
                   EMDASH_LP_TIMEOUT="1s")
        # Escaping timeout's process group must not escape the systemd scope.
        # The child also exits by itself after four seconds if the guard fails.
        marker = "emdash-guard-detached-child-test"
        code = ("import subprocess, sys, time; "
                "child = subprocess.Popen([sys.executable, '-c', "
                "'import time; time.sleep(4)', sys.argv[1]], "
                "start_new_session=True); "
                "print(child.pid, flush=True); time.sleep(4)")
        started = time.monotonic()
        first = subprocess.Popen(
            ["bash", str(GUARD), "python3", "-c", code, marker], env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        child_pid = None
        try:
            child_pid = int(first.stdout.readline().strip())
            _, errors = first.communicate(timeout=6)
            self.assertNotEqual(first.returncode, 0, errors)
            self.assertLess(time.monotonic() - started, 3)
            # A reparented zombie is dead even if its /proc entry still exists.
            stat = Path(f"/proc/{child_pid}/stat")
            if stat.exists():
                self.assertEqual(stat.read_text().split(")", 1)[1].split()[0], "Z")
        finally:
            if first.poll() is None:
                first.kill()
                first.communicate(timeout=6)
            if child_pid is not None:
                cmdline = Path(f"/proc/{child_pid}/cmdline")
                try:
                    if marker.encode() in cmdline.read_bytes():
                        os.kill(child_pid, signal.SIGKILL)
                except (FileNotFoundError, ProcessLookupError):
                    pass


if __name__ == "__main__":
    unittest.main()
