const userAgent = process.env.npm_config_user_agent ?? '';

if (!userAgent.startsWith('pnpm/')) {
  console.error('This contributor workspace uses pnpm, not npm.');
  console.error('Run ./scripts/pnpmw install --frozen-lockfile from the Git root.');
  process.exit(1);
}
