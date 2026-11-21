### Written plans declare only the functions they call

A plan the checker writes (`--write`, a report's `optimized`, the plan to run and the assumed issues' check) used to declare all 153 functions sverify knows, about 11 KB of each plan. It now declares only those it calls, so a written plan is 0.6–3.3 KB where it was 11–13 KB, and the contract goldens' answers are 75 KB where they were 196 KB (#1787). A plan's digest is unchanged: it never read the declarations (`plan_digest`).
