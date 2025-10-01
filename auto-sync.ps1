# Requires: PowerShell 5+ and Git available on PATH
Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Ensure-GitAvailable {
    if (-not (Get-Command git -ErrorAction SilentlyContinue)) {
        throw "Git is not installed or not available on PATH."
    }
}

try {
    Ensure-GitAvailable

    if (Get-Variable -Name PSScriptRoot -ErrorAction SilentlyContinue) {
        Set-Location -Path $PSScriptRoot
    }

    Write-Host "Working directory:" (Get-Location)

    $changes = git status --porcelain
    if (-not $changes) {
        Write-Host "No changes detected. Nothing to commit." -ForegroundColor Yellow
        exit 0
    }

    git add .

    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $commitMessage = "Auto sync $timestamp"

    git commit -m $commitMessage
    if ($LASTEXITCODE -ne 0) {
        throw "git commit failed with exit code $LASTEXITCODE"
    }

    git push
    if ($LASTEXITCODE -ne 0) {
        throw "git push failed with exit code $LASTEXITCODE"
    }

    Write-Host "Repository successfully synced." -ForegroundColor Green
}
catch {
    Write-Error $_
    exit 1
}
