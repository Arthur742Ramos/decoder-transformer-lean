# Reproducible dependencies

The concrete IEEE theory is intentionally kept separate from the source tree,
but its dependency is pinned so a clean checkout can be rebuilt without a
machine-specific path.

## Required versions

| Dependency | Version | SHA-256 |
| --- | --- | --- |
| Isabelle | `Isabelle2025-2` | Use the official Isabelle distribution checksum for the selected platform. |
| AFP `IEEE_Floating_Point` | release `2026-02-06` | `6194f58afd31a8acf1b8097e7049938590e8459f94f22ad9fe83122448d6942a` |
| AFP `Word_Lib` | release `2026-02-06` | `a52c0eea0b980f0fd1d3eaa83360eb719c976228308e57d494afcecb7943971a` |

Download URLs:

- <https://www.isa-afp.org/release/afp-IEEE_Floating_Point-2026-02-06.tar.gz>
- <https://www.isa-afp.org/release/afp-Word_Lib-2026-02-06.tar.gz>

The archive hashes above are content hashes of the downloaded tarballs.  The
AFP entry itself is BSD-licensed; retain its accompanying license metadata
when redistributing the dependency.

## Expected layout

Extract both archives below one directory named `decoder-transformer-afp`:

```text
decoder-transformer-afp/
  IEEE_Floating_Point/ROOT
  Word_Lib/ROOT
```

For an AFP checkout whose sessions live below `thys`, point the helper at the
checkout root instead; it searches both the root and its `thys` directory.

## Windows setup and verification

```powershell
$afpRoot = "C:\path\to\decoder-transformer-afp"
$env:DECODER_TRANSFORMER_AFP_ROOT = $afpRoot

Get-FileHash .\afp-IEEE_Floating_Point-2026-02-06.tar.gz -Algorithm SHA256
Get-FileHash .\afp-Word_Lib-2026-02-06.tar.gz -Algorithm SHA256

cd Q:\src\isabelle-afp-monorepo-transformer\projects\decoder-transformer-isabelle
.\tools\build.ps1 -NoDocument
```

The proof-only build must finish with `isabelle build OK
(Decoder_Transformer)`.  Run the same wrapper without `-NoDocument` before an
AFP submission.
