param(
 [Parameter(Mandatory=$true)][string]$Manifest,
 [Parameter(Mandatory=$true)][string]$RootPair,
 [Parameter(Mandatory=$true)][string]$AuditLog,
 [Parameter(Mandatory=$true)][string]$ControlLog,
 [Parameter(Mandatory=$true)][string]$Tag,
 [string]$PriorAcceptance='ACCEPTANCE-A8-FRAMEWORK-CONTINUE-20261005.json',
 [int]$PriorTotal=44,[int]$ExpectedTotal=62,[int]$MinimumSources=1319,
 [string]$PaidDescription='actual local polygon/facet/refinement geometry; embedded dual skeleton; true-nearest ear q<=1; exact2 hub vertices',
 [string]$UnpaidDescription='global cellular dual disk, global coherent triangle complex and two-fan/metric classification',
 [string[]]$AdditionalAuditNeedles=@())
$ErrorActionPreference='Stop'
$project=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$outPath=Join-Path $PSScriptRoot "ACCEPTANCE-$Tag.json"
if(Test-Path -LiteralPath $outPath){throw 'Append-only acceptance already exists'}
$prior=Join-Path $PSScriptRoot $PriorAcceptance
$a8=Get-Content -LiteralPath $prior -Raw|ConvertFrom-Json
if($a8.paid_framework_modules -ne $PriorTotal -or $a8.unconditional_n11_complete){throw 'Invalid accepted baseline'}
$root=Join-Path $project 'lean\N11Formalization.lean'
$sha=(Get-FileHash -LiteralPath $root).Hash
$m=Get-Content -LiteralPath $Manifest -Raw|ConvertFrom-Json
if($m.project -ne $project -or $m.root_sha256 -ne $sha -or $m.modules_total -ne $ExpectedTotal -or
   $m.modules_green -ne $ExpectedTotal -or $m.incomplete_modules.Count){throw 'Bad module manifest'}
foreach($row in $m.modules){
 if(!$row.module_green -or !$row.standard_axioms_only -or
   (Get-FileHash -LiteralPath $row.source).Hash -ne $row.sha256){throw "Module source/audit drift $($row.module)"}
}
$pair=@(Get-Content -LiteralPath $RootPair -Raw|ConvertFrom-Json)
if($pair.Count -ne 2){throw 'Exactly two root runs required'}
foreach($r in $pair){
 if($r.exit -ne 0 -or !$r.unchanged -or $r.changed_sources.Count -or
    $r.root_sha256_before -ne $sha -or $r.root_sha256_after -ne $sha -or
    $r.source_scope -ne 'all owned Lean sources below lean excluding .lake dependencies/build artifacts' -or
    $r.source_count -lt $MinimumSources){throw 'Bad frozen root pair'}
}
$evidence=@()
foreach($log in @($AuditLog,$ControlLog)){
 $r=Get-Content -LiteralPath "$log.result.json" -Raw|ConvertFrom-Json
 if($r.exit -ne 0 -or !$r.unchanged -or $r.build -or $r.project -ne (Join-Path $project 'lean')){throw 'Bad probe result'}
 $source=if([IO.Path]::IsPathRooted($r.file)){$r.file}else{Join-Path (Join-Path $project 'lean') $r.file}
 $s=(Get-FileHash -LiteralPath $source).Hash
 if($s -ne $r.sha256_before -or $s -ne $r.sha256_after){throw 'Probe source drift'}
 $text=Get-Content -LiteralPath $log -Raw
 if($text -match 'sorryAx|native_decide|Lean\.ofReduceBool|error:'){throw 'Forbidden/failing probe'}
 $hits=[regex]::Matches($text,'depends on axioms:\s*\[([^\]]*)\]','Singleline')
 if(!$hits.Count){throw 'No axiom audit'}
 foreach($hit in $hits){foreach($a in ($hit.Groups[1].Value -split ',')){
   if($a.Trim() -and $a.Trim() -notin @('propext','Classical.choice','Quot.sound')){throw 'Unpermitted axiom'}
 }}
 $evidence+=[ordered]@{log=$log;log_sha256=(Get-FileHash -LiteralPath $log).Hash;source=$source;source_sha256=$s}
}
$audit=Get-Content -LiteralPath $AuditLog -Raw
foreach($needle in (@('still_explicit_main_consumer','RemainingSourceObligation','RemainingTerminalRadius',
 'Canonical33Obligation','CanonicalNearest33Obligation','sourceRoot 6','source_attainment',
 'actual_nearest_ear_count','distinct_bridge_spokes_intersection','positive_facet_retained','hub_vertices_card')+
 $AdditionalAuditNeedles)){
 if(!$audit.Contains($needle)){throw "Missing actual root consumer/interface $needle"}
}
$control=Get-Content -LiteralPath $ControlLog -Raw
foreach($needle in @('crossing_diagonals_true_common_nearest','no_diagonal_positive_facet','large_empty_arc_support')){
 if(!$control.Contains($needle)){throw "Missing negative control $needle"}
}
$out=[ordered]@{claim=$Tag;timestamp=(Get-Date).ToString('o');project=$project;
 root_sha256=$sha;prior_acceptance=$prior;manifest=$Manifest;root_pair=$RootPair;
 paid_framework_modules=$ExpectedTotal;new_modules=($ExpectedTotal-$PriorTotal);unconditional_n11_complete=$false;
 source='SAME C891 boxed TC/KKT12 unique root,coordinate6;full arbitrary Fin11 Covers';
 unchanged_historical_counts=$a8.unchanged_historical_counts;unpaid=$a8.unpaid;
 new_paid=$PaidDescription;not_paid=$UnpaidDescription;
 evidence=$evidence;allowed_axioms=@('propext','Classical.choice','Quot.sound')}
$out|ConvertTo-Json -Depth 8|Set-Content -LiteralPath $outPath -Encoding utf8
Write-Output "A9 framework accepted=$outPath; unconditional_n11_complete=false"
