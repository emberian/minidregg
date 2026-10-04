# The Mini project site

Static pages for GitHub Pages: plain HTML and one stylesheet (`site.css`, light and dark),
no JavaScript, no external fonts or scripts.

| Page | Content |
| --- | --- |
| `index.html` | what Mini is, who it is for, its state in one paragraph |
| `language.html` | Objective Bend: Core4, two tutorial programs, what is and is not proved |
| `architecture.html` | admission, store and laws, receipts, SDK, private rooms, agreement, what is not done |
| `status.html` | **generated**: the README's Honest state table (`gen-status.py`) |
| `join.html` | a pointer to `deploy/shell/FRIENDS.md` and what a newcomer can do today |

## Rules

- Every factual sentence comes from a file at main, and `SOURCES.md` maps it to file and
  lines. When a source changes, change the page and the map together. Where a page and
  the repository disagree, the repository is right.
- Never edit `status.html`. Edit the Honest state table in `README.md`, then run
  `python3 website/gen-status.py`. The header and footer are copied from `index.html`.
- A code block marked `<pre data-source="PATH">` must be text of `PATH`.
- `python3 website/gen-status.py --check` (the `website` row of `scripts/local-gates.sh`,
  and a step of `.github/workflows/pages.yml`) fails on a stale status page or a drifted
  code block, and runs two controls that must be refused.

## Deploy

`.github/workflows/pages.yml` publishes this directory on every push to `main` that
touches `website/` or `README.md`, after the check passes. Local preview: open
`index.html`, or `python3 -m http.server -d website 8080`.
