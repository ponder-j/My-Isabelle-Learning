#!/usr/bin/env zsh

# Requires: zsh and Git available on PATH
set -euo pipefail

# Function to ensure Git is available
ensure_git_available() {
    if ! command -v git >/dev/null 2>&1; then
        echo "Error: Git is not installed or not available on PATH." >&2
        exit 1
    fi
}

# Function to print colored output
print_color() {
    local color=$1
    local message=$2
    case $color in
        "yellow") echo "\033[33m$message\033[0m" ;;
        "green") echo "\033[32m$message\033[0m" ;;
        "red") echo "\033[31m$message\033[0m" ;;
        *) echo "$message" ;;
    esac
}

# Main execution
main() {
    ensure_git_available

    # Change to script directory if possible
    if [[ -n "${0:A:h}" ]]; then
        cd "${0:A:h}"
    fi

    echo "Working directory: $(pwd)"

    # Check for changes
    local changes=$(git status --porcelain)
    if [[ -z "$changes" ]]; then
        print_color "yellow" "No changes detected. Nothing to commit."
        exit 0
    fi

    # Add all changes
    git add .

    # Create commit message with timestamp
    local timestamp=$(date "+%Y-%m-%d %H:%M:%S")
    local commit_message="Auto sync $timestamp"

    # Commit changes
    if ! git commit -m "$commit_message"; then
        print_color "red" "git commit failed"
        exit 1
    fi

    # Push changes
    if ! git push; then
        print_color "red" "git push failed"
        exit 1
    fi

    print_color "green" "Repository successfully synced."
}

# Error handling
trap 'print_color "red" "Script failed on line $LINENO"' ERR

# Run main function
main "$@"