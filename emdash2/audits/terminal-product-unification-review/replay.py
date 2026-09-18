#!/usr/bin/env python3
"""Rebuild isolated review sources; never edit owners or invoke the checker."""
from pathlib import Path
import hashlib
import json


def main() -> None:
    audit = Path(__file__).resolve().parent
    root = audit.parents[1]
    manifest = json.loads((audit / 'manifest.json').read_text())
    base = (root / manifest['owner']).read_text()
    if hashlib.sha256(base.encode()).hexdigest() != manifest['owner_sha256']:
        raise SystemExit('Owner changed: review/rebase this experiment explicitly.')
    output = root / 'tmp/probes'
    output.mkdir(parents=True, exist_ok=True)
    terminal = 'constant symbol Terminal_obj : τ (Obj Terminal_cat);'
    sigma = 'rule sigma_Snd (Struct_sigma _ $2) ↪ $2;'
    if base.count(terminal) != 1 or base.count(sigma) != 1:
        raise SystemExit('Expected unique owning declaration positions.')
    terminal_rule = '\nunif_rule $x ≡ Terminal_obj ↪ [ tt ≡ tt ];\n'
    product_rule = ('\nunif_rule $x ≡ Struct_sigma $x1 $x2 ↪ '
                    '[ sigma_Fst $x ≡ $x1; sigma_Snd $x ≡ $x2 ];\n')

    def write(name: str, source: str, fragment: str) -> None:
        suffix = (audit / fragment).read_text()
        target = output / ('replay_' + name + '.lp')
        target.write_text(source + '\n' + suffix)
        print(target.relative_to(root))

    for rigidity in ('constant', 'injective'):
        declaration = terminal.replace('constant', rigidity, 1)
        owner = base.replace(terminal, declaration)
        for mode in ('candidate', 'control'):
            source = (owner.replace(declaration, declaration + terminal_rule)
                      if mode == 'candidate' else owner)
            write('terminal_' + rigidity + '_' + mode, source, 'terminal.lpfragment')
    for case in ('observations', 'observer', 'reverse', 'inference'):
        for mode in ('candidate', 'control'):
            source = base.replace(sigma, sigma + product_rule) if mode == 'candidate' else base
            write('product_' + case + '_' + mode, source, 'product-' + case + '.lpfragment')


if __name__ == '__main__':
    main()
