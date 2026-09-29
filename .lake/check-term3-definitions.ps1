$ErrorActionPreference = 'Stop'
$taskRoot = 'F:/projects/leanprojects/wellfound/Multi'
$baseline = [IO.File]::ReadAllText((Join-Path $taskRoot '.lake/term3-wellfounded-request-original.lean')).Replace("`r`n", "`n")
$current = [IO.File]::ReadAllText((Join-Path $taskRoot 'Multi/Term3Syntax.lean'))
function Normalize-Term3Declaration([string]$text) {
  $text = [regex]::Replace($text, '(?s)/\-.*?\-/', '')
  $text = [regex]::Replace($text, '(?m)--.*$', '')
  return [regex]::Replace($text, '\s+', ' ').Trim()
}
$commands = [regex]::Matches($baseline, '(?m)^(?:def|inductive|instance|theorem|namespace|end|open|import|set_option|#print)\b.*')
$normalizedCurrent = Normalize-Term3Declaration $current
$count = 0
for ($i = 0; $i -lt $commands.Count; $i++) {
  $entry = $commands[$i]
  if ($entry.Value -notmatch '^(def|inductive|instance)\b') { continue }
  $endOffset = $baseline.Length
  if ($i + 1 -lt $commands.Count) { $endOffset = $commands[$i + 1].Index }
  $declSource = $baseline.Substring($entry.Index, $endOffset - $entry.Index)
  $decreasing = $declSource.IndexOf('decreasing_by')
  if ($decreasing -ge 0) { $declSource = $declSource.Substring(0, $decreasing) }
  $decl = Normalize-Term3Declaration $declSource
  if (-not $normalizedCurrent.Contains($decl)) { throw "Definition changed: $($entry.Value)" }
  $count++
}
Write-Output "Verified $count original definition / inductive / instance declarations unchanged (ignoring whitespace, comments, and termination proof scripts)."
