#!/bin/bash

# CIP Auto-Formatter
# Automatically formats CIP documents and checks for issues
# Similar to prettier but for CIP-specific formatting rules

set -euo pipefail

TARGET_FILE="${1:-docs/cip/README.md}"

if [[ ! -f "$TARGET_FILE" ]]; then
    echo "❌ File $TARGET_FILE not found"
    exit 1
fi

echo "🔧 Formatting CIP document: $TARGET_FILE"

# Make backup
cp "$TARGET_FILE" "${TARGET_FILE}.bak"

# 1. Format figure captions to consistent <em> tags
echo "  ├─ Standardizing figure captions..."

# Convert underscore format: _Figure X: Caption_ -> <em>Figure X: Caption</em>
sed -i.tmp 's/^_\(Figure [0-9]\+[:.] .*\)_$/<em>\1<\/em>/g' "$TARGET_FILE"

# Convert sub tags for figure captions: <sub>Figure X: Caption</sub> -> <em>Figure X: Caption</em>
sed -i.tmp 's/^<sub>\(Figure [0-9]\+: .*\)<\/sub>$/<em>\1<\/em>/g' "$TARGET_FILE"

# Normalize periods to colons in figure captions
sed -i.tmp 's/<em>\(Figure [0-9]\+\)\. \(.*\)<\/em>/<em>\1: \2<\/em>/g' "$TARGET_FILE"

# Clean up temp file
rm -f "${TARGET_FILE}.tmp"

# 2. Basic validation checks
echo "  ├─ Running validation checks..."

BROKEN_LINKS=0

# Count figures in TOC vs actual captions
TOC_FIGURES=$(grep -c '^\s*- \[Figure [0-9]\+:' "$TARGET_FILE" || true)
CAPTION_FIGURES=$(grep -c '^<em>Figure [0-9]\+:' "$TARGET_FILE" || true)

if [[ $TOC_FIGURES -ne $CAPTION_FIGURES ]]; then
    echo "    ⚠️  Figure count mismatch: $TOC_FIGURES in TOC, $CAPTION_FIGURES captions found"
    BROKEN_LINKS=1
fi

# 3. Check for issues that couldn't be auto-fixed
echo "  ├─ Checking for remaining issues..."

ISSUES_FOUND=0

# Check for any remaining underscore figure captions
if grep -q '^_Figure [0-9]\+:.*_$' "$TARGET_FILE"; then
    echo "    ⚠️  Some underscore figure captions couldn't be auto-fixed"
    ISSUES_FOUND=1
fi

# 4. Show summary
echo "  └─ Formatting complete"

if [[ $BROKEN_LINKS -eq 0 && $ISSUES_FOUND -eq 0 ]]; then
    echo "✅ Document formatted successfully, no issues found"
    rm -f "${TARGET_FILE}.bak"
    exit 0
else
    echo "⚠️  Document formatted with warnings (see above)"
    if [[ $BROKEN_LINKS -eq 1 ]]; then
        echo "    Links may need manual review"
    fi
    if [[ $ISSUES_FOUND -eq 1 ]]; then
        echo "    Some formatting issues may need manual attention"
    fi
    rm -f "${TARGET_FILE}.bak"
    exit 0  # Don't fail the workflow for warnings
fi
