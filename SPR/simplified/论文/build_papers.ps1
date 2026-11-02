param(
    [string]$BuildDirectory = (Join-Path $PSScriptRoot '.build')
)
$ErrorActionPreference = 'Stop'
$papers = @('n3_formalization', 'n4_formalization', 'n5_alternative_proof', 'n6_alternative_proof')
$buildRoot = [System.IO.Path]::GetFullPath($BuildDirectory)
New-Item -ItemType Directory -Path $buildRoot -Force | Out-Null
Push-Location -LiteralPath $PSScriptRoot
try {
    foreach ($paper in $papers) {
        $paperBuild = Join-Path $buildRoot $paper
        New-Item -ItemType Directory -Path $paperBuild -Force | Out-Null
        for ($pass = 1; $pass -le 3; $pass++) {
            & xelatex '-interaction=nonstopmode' '-halt-on-error' "-output-directory=$paperBuild" "$paper.tex" *> (Join-Path $paperBuild "console-$pass.txt")
            if ($LASTEXITCODE -ne 0) { throw "XeLaTeX failed: $paper, pass $pass. See $paperBuild." }
            if ($pass -eq 1) {
                # A local database avoids BibTeX's restrictions on absolute output paths.
                Copy-Item -LiteralPath (Join-Path $PSScriptRoot 'spr_references.bib') -Destination $paperBuild -Force
                Push-Location -LiteralPath $paperBuild
                try {
                    & bibtex $paper *> 'bibtex-console.txt'
                    if ($LASTEXITCODE -ne 0) { throw "BibTeX failed: $paper. See $paperBuild." }
                } finally {
                    Pop-Location
                }
                $bibLog = Get-Content -LiteralPath (Join-Path $paperBuild "$paper.blg") -Raw
                if ($bibLog -match 'Warning--|error message|I couldn.t open') {
                    throw "Bibliography warning in $paper. Inspect $paperBuild."
                }
            }
        }
        $log = Get-Content -LiteralPath (Join-Path $paperBuild "$paper.log") -Raw
        if ($log -match 'Overfull \\[hv]box|undefined references|Citation .+ undefined|Reference .+ undefined|Missing character:|Rerun to get cross-references right') {
            throw "Unresolved layout or reference warning in $paper. Inspect $paperBuild."
        }
        $outputName = "$paper.pdf"
        Copy-Item -LiteralPath (Join-Path $paperBuild "$paper.pdf") -Destination (Join-Path $PSScriptRoot $outputName) -Force
        Write-Output "Built $outputName"
    }
} finally {
    Pop-Location
}
