# Publication review

Reviewed 2026-11-23 before publication.

The original ZIP and the prepared repository payload were checked for
credential signatures, private keys, credential assignments, email addresses,
lease identifiers, absolute Windows paths, and user home-directory paths.
The final release archive is scanned again before uploading. The reproducible
heuristic scanner is `scan_publication.py`; it reports filenames and categories
without exposing matched content. Pattern definitions in that scanner are
excluded from scanning itself and were reviewed manually.

No credentials, private personal information, live lease IDs, or actual
machine-specific paths were found. Public upstream repository URLs and the
owner's intentionally public GitHub repository name are retained. Generic
verification examples such as `/absolute/path/to/...` are placeholders, not
paths from the research machine. The full Lean source, data, logs, and
upstream snapshots were reviewed for publication scope. Interpreter caches,
local tool installations, authentication state, and Git internals are excluded.

The repository uses a GitHub noreply commit identity to avoid exposing a
private email address. No claim is made that heuristic scanning can prove
the absence of every possible sensitive string.

This work is explicitly AI-assisted, is a verified computational research
artifact, and makes no lower-bound, breakthrough, or mathematical novelty claim.
