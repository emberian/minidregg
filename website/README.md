# minidregg project site

Static multi-page site for GitHub Pages. No build step — HTML + CSS only.

| Page | Role |
|---|---|
| `index.html` | thesis, four pillars, honesty policy |
| `why.html` | breadstuffs diagnosis + founding inversion |
| `architecture.html` | narrow waist, repo carve, pillar detail |
| `maturity.html` | S/A/P/D/B legend + current residuals |
| `laws.html` | sixteen ATLAS design laws |

## Deploy

On push to `main` (when `website/**` changes), `.github/workflows/pages.yml` uploads
this directory as the Pages artifact.

One-time repo setup (owner):

```bash
gh api -X POST repos/emberian/minidregg/pages \
  -f build_type=workflow \
  -f source[branch]=main \
  -f source[path]=/
# or: Settings → Pages → Source: GitHub Actions
```

Local preview: open `index.html` in a browser, or

```bash
python3 -m http.server -d website 8080
```

## Editing

Keep maturity claims synchronized with the root `README.md` / `GOAL.md`. Prefer
pessimistic labels over marketing prose. Relative links only (project Pages live at
`/minidregg/`).
