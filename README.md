# formal-syncordian

[![CI](https://github.com/jonaprieto/formal-syncordian/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/formal-syncordian/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.33.0-blue)](https://lean-lang.org)

Lean 4 formalization of [Syncordian](https://github.com/Masanar/Syncordian): dense
positions, the line status lattice, and the document model.

```bash
lake build
```

| Module | Contents |
| --- | --- |
| `Syncordian/Position.lean` | `PositionSpec`: the dense total order, no representation |
| `Syncordian/PathId.lean` | A candidate model: sentinels plus lexicographic segments |
| `Syncordian/Status.lean` | Line lifecycle chain, forward-only transitions |
| `Syncordian/Line.lean` | Line identity, write-once data, mutable state |
| `Syncordian/Document.lean` | Document as a list of lines, well-formedness |
