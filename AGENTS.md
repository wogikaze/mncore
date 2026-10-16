# AGENTS.md

## Search Tools
- **Code search**: prefer `ig` (instant-grep) over `rg` or `grep` for searching code.
- Usage: `ig "pattern" [path]` or `ig search "pattern" [path]` — trigram-indexed regex search.
- If the project has no `.ig/` index yet, `ig` auto-builds one on first search.
- Fall back to `rg` only if `ig` is not installed.

## Commit Rules

- Make one commit for one coherent, reviewable outcome, rather than committing each lemma, intermediate connection, or small implementation step.
- Keep a feature's implementation, its proof or regression coverage, and related generated catalogs or hashes together when they form one deliverable.
- Split work only when a part is independently useful and reviewable, or when it is a prerequisite that can land on its own.
- Include a fix and the check that guards against its regression in the same commit.
- Before committing, run the relevant build or verification for the changed area and update any generated artifacts affected by the change.
- Use a concise commit subject that describes the user-visible or proof-level outcome. Explain broader scope in the commit body when needed.
- Keep in-progress work uncommitted until it forms a coherent outcome; do not create commits solely to checkpoint tiny steps.
