# DEVELOPMENT

## Regenerate

```bash
python docs/scripts/organize_mncore_docs.py
```

## Input/Output

- Input: `docs/mncore.json` (Cosense JSON export)
- Output root: `docs/mncore_llm`

## Output Details

- `chapters/chXX/`: chapter title page + numbered section pages
- `topics/<bucket>/`: non-numbered pages
- `indexes/chapter_index.md`: chapter tree
- `indexes/topic_index.md`: topic files grouped by bucket
- `indexes/title_to_path.json`: title -> [path]
- `indexes/id_to_path.json`: page id -> path
- `indexes/link_graph.json`: title -> referenced [[titles]]

## Notes

- File names include `__<id8>` to avoid collisions.
- Section file names use `section-<number>` for stable numeric retrieval.
