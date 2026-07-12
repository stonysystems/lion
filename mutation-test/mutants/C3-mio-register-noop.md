crate: lion-reactor
# C3 (control, trusted region) — mio registration body does nothing

**Target**: the `registry.register(...)` call inside
`register_io_source_action` (external_body) in `ext.rs`.
**Mutation**: skip the real registration and return Ok(()).
**Liveness violation**: the OS never delivers readiness for that fd — the io
wake chain is severed at its source.
**Prediction**: **SURVIVED** (the ensures describe only the log shape and field
frame; the real mio effect is declared trust residue). Stress io loads hang.
