#!/bin/bash

# CIP Auto-Formatter
# Automatically formats CIP documents using Prettier and checks for issues

set -euo pipefail

TARGET_FILE="${1:-docs/cip/README.md}"

if [[ ! -f "$TARGET_FILE" ]]; then
    echo "❌ File $TARGET_FILE not found"
    exit 1
fi

echo "🔧 Formatting CIP document: $TARGET_FILE"

# Make backup
cp "$TARGET_FILE" "${TARGET_FILE}.bak"

# 1. Format figure and table captions to consistent <em> tags
echo "  ├─ Standardizing figure and table captions..."

# Convert underscore format: _Figure X: Caption_ -> <em>Figure X: Caption</em>
sed -i.tmp 's/^_\(Figure [0-9]\+[:.] .*\)_$/<em>\1<\/em>/g' "$TARGET_FILE"

# Convert sub tags for figure captions: <sub>Figure X: Caption</sub> -> <em>Figure X: Caption</em>
sed -i.tmp 's/^<sub>\(Figure [0-9]\+: .*\)<\/sub>$/<em>\1<\/em>/g' "$TARGET_FILE"

# Normalize periods to colons in figure captions
sed -i.tmp 's/<em>\(Figure [0-9]\+\)\. \(.*\)<\/em>/<em>\1: \2<\/em>/g' "$TARGET_FILE"

# Convert table captions to consistent <em> format (colon and period formats)
sed -i.tmp 's/^_\(Table [0-9][0-9]*[:.] .*\)_$/<em>\1<\/em>/g' "$TARGET_FILE"

# Normalize periods to colons in table captions
sed -i.tmp 's/<em>\(Table [0-9][0-9]*\)\. \(.*\)<\/em>/<em>\1: \2<\/em>/g' "$TARGET_FILE"

# Remove trailing periods from figure and table captions for consistency
sed -i.tmp 's/<em>\(Figure [0-9][0-9]*: .*\)\.<\/em>/<em>\1<\/em>/g' "$TARGET_FILE"
sed -i.tmp 's/<em>\(Table [0-9][0-9]*: .*\)\.<\/em>/<em>\1<\/em>/g' "$TARGET_FILE"


# Clean up temp file
rm -f "${TARGET_FILE}.tmp"

# 2. Generate table of contents from headers
echo "  ├─ Generating table of contents..."

# Generate TOC using Python
python3 - "$TARGET_FILE" << 'EOF'
import sys
import re

def generate_anchor(text):
    """Convert header text to GitHub-style anchor"""
    # Convert to lowercase
    anchor = text.lower()
    # Replace spaces and special chars with hyphens
    anchor = re.sub(r'[^\w\s-]', '', anchor)
    anchor = re.sub(r'[-\s]+', '-', anchor)
    # Remove leading/trailing hyphens
    anchor = anchor.strip('-')
    return anchor

def generate_toc(content):
    """Generate table of contents from markdown headers"""
    lines = content.split('\n')
    toc_lines = []
    
    for line in lines:
        # Match headers (## to ####)
        match = re.match(r'^(#{2,4})\s+(.+)$', line.strip())
        if match:
            level = len(match.group(1))
            title = match.group(2).strip()
            
            # Skip organizational headers that shouldn't be in main TOC
            skip_titles = ['figures', 'tables', 'table of contents', 'table of figures and tables']
            if title.lower() in skip_titles:
                continue
            
            # Generate anchor
            anchor = generate_anchor(title)
            
            # Create indentation based on header level
            indent = '  ' * (level - 2)  # h2 = no indent, h3 = 2 spaces, h4 = 4 spaces
            
            # Format as markdown link
            toc_line = f"{indent}- [{title}](#{anchor})"
            toc_lines.append(toc_line)
    
    return '\n'.join(toc_lines)

# Read the file
with open(sys.argv[1], 'r') as f:
    content = f.read()

# Generate TOC
toc = generate_toc(content)

# Replace the existing TOC placeholder
toc_replacement = f"""<details>
  <summary><h2>Table of contents</h2></summary>

{toc}

</details>"""

# Find and replace the TOC section
# Pattern: <details>\s*<summary><h2>Table of contents</h2></summary>.*?</details>
pattern = r'<details>\s*<summary><h2>Table of contents</h2></summary>.*?</details>'
content = re.sub(pattern, toc_replacement, content, flags=re.DOTALL)

# Write back
with open(sys.argv[1], 'w') as f:
    f.write(content)
EOF

# Generate table of figures and tables
echo "  ├─ Generating table of figures and tables..."

python3 - "$TARGET_FILE" << 'EOF'
import sys
import re

def generate_anchor_from_figure(figure_text):
    """Generate anchor for figure based on figure number"""
    # Extract figure number
    match = re.search(r'Figure (\d+)', figure_text)
    if match:
        return f"figure-{match.group(1)}"
    return ""

def generate_table_of_figures_and_tables(content):
    """Generate table of figures and tables from document content"""
    # Use regex to find all figure and table captions, including multi-line ones
    figures = []
    tables = []
    
    # Find all figure captions (including multi-line)
    figure_pattern = r'<em>(Figure \d+: [^<]+)</em>'
    figure_matches = re.findall(figure_pattern, content, re.DOTALL)
    
    for match in figure_matches:
        caption = match.strip()
        # Remove line breaks and normalize whitespace
        caption = re.sub(r'\s+', ' ', caption).strip()
        # Escape LaTeX formulas to prevent Prettier from mangling them
        caption_escaped = caption.replace('\\', '\\\\')
        anchor = generate_anchor_from_figure(caption)
        if anchor:
            figures.append(f"- [{caption_escaped}](#{anchor})")
    
    # Find all table captions (including multi-line)
    table_pattern = r'<em>(Table \d+: [^<]+)</em>'
    table_matches = re.findall(table_pattern, content, re.DOTALL)
    
    for match in table_matches:
        caption = match.strip()
        # Remove line breaks and normalize whitespace
        caption = re.sub(r'\s+', ' ', caption).strip()
        # Escape LaTeX formulas to prevent Prettier from mangling them
        caption_escaped = caption.replace('\\', '\\\\')
        # Extract table number for anchor
        table_num_match = re.search(r'Table (\d+)', caption)
        if table_num_match:
            anchor = f"table-{table_num_match.group(1)}"
            tables.append(f"- [{caption_escaped}](#{anchor})")
    
    # Sort figures and tables by number
    def extract_number(item):
        """Extract number from figure/table item for sorting"""
        match = re.search(r'(Figure|Table) (\d+):', item)
        if match:
            return int(match.group(2))
        return 0
    
    figures.sort(key=extract_number)
    tables.sort(key=extract_number)
    
    # Build the figures and tables section
    result = []
    result.append("### Figures")
    result.append("")
    if figures:
        result.extend(figures)
    else:
        result.append("No figures found.")
    result.append("")
    result.append("### Tables")
    result.append("")
    if tables:
        result.extend(tables)
    else:
        result.append("No tables found.")
    
    return '\n'.join(result)

# Read the file
with open(sys.argv[1], 'r') as f:
    content = f.read()

# Generate table of figures and tables
fig_table_content = generate_table_of_figures_and_tables(content)

# Replace the existing table of figures and tables section
fig_table_replacement = f"""<details>
  <summary><h2>Table of figures and tables</h2></summary>

{fig_table_content}

</details>"""

# Find and replace the table of figures section
# Pattern: <details>\s*<summary><h2>Table of figures and tables</h2></summary>.*?</details>
pattern = r'<details>\s*<summary><h2>Table of figures and tables</h2></summary>.*?</details>'
content = re.sub(pattern, fig_table_replacement, content, flags=re.DOTALL)

# Write back
with open(sys.argv[1], 'w') as f:
    f.write(content)
EOF

# 3. Format with Prettier using a less aggressive configuration
echo "  ├─ Formatting with Prettier..."

# Check if prettier is available, install if needed
if ! command -v npx &> /dev/null; then
    echo "    ❌ npx not found. Please install Node.js"
    exit 1
fi

# Create a prettier config that's more conservative with markdown
cat > .prettierrc.json << EOF
{
  "proseWrap": "always",
  "printWidth": 80,
  "tabWidth": 2,
  "useTabs": false,
  "overrides": [
    {
      "files": "*.md",
      "options": {
        "proseWrap": "always",
        "printWidth": 80,
        "endOfLine": "lf"
      }
    }
  ]
}
EOF

# Run prettier
npx prettier --config .prettierrc.json --write "$TARGET_FILE"

# Clean up temp config
rm -f .prettierrc.json

# 3. Post-process to fix markdown alerts that might have been incorrectly wrapped
echo "  ├─ Fixing markdown alert formatting..."

# Use a more targeted Python script to fix alert formatting
python3 - "$TARGET_FILE" << 'EOF'
import sys
import re

# Read the file
with open(sys.argv[1], 'r') as f:
    content = f.read()

# Fix markdown alerts that got broken by prettier
# Pattern 1: > [!TYPE] **Title**: content -> > [!TYPE]\n>\n> **Title**: content
content = re.sub(
    r'^> \[!(NOTE|WARNING|IMPORTANT|CAUTION)\] \*\*([^*]+)\*\*:(.*)$',
    r'> [!\1]\n>\n> **\2**:\3',
    content,
    flags=re.MULTILINE
)

# Pattern 2: > [!TYPE] **Title** (no colon) -> > [!TYPE]\n>\n> **Title**
content = re.sub(
    r'^> \[!(NOTE|WARNING|IMPORTANT|CAUTION)\] \*\*([^*]+)\*\*$',
    r'> [!\1]\n>\n> **\2**',
    content,
    flags=re.MULTILINE
)

# Pattern 3: > [!TYPE] content (without bold title) -> > [!TYPE]\n>\n> content
content = re.sub(
    r'^> \[!(NOTE|WARNING|IMPORTANT|CAUTION)\] ([^*\n].*)$',
    r'> [!\1]\n>\n> \2',
    content,
    flags=re.MULTILINE
)

# Write back
with open(sys.argv[1], 'w') as f:
    f.write(content)
EOF

# 4. Basic validation checks
echo "  ├─ Running validation checks..."

BROKEN_LINKS=0

# Count figures in table of figures vs actual captions
TABLE_FIGURES=$(grep -c '^\s*- \[Figure [0-9]\+:' "$TARGET_FILE" || true)
CAPTION_FIGURES=$(grep -c '^<em>Figure [0-9]\+:' "$TARGET_FILE" || true)

if [[ $TABLE_FIGURES -ne $CAPTION_FIGURES ]]; then
    echo "    ⚠️  Figure count mismatch: $TABLE_FIGURES in table of figures, $CAPTION_FIGURES captions found"
    BROKEN_LINKS=1
fi

# 5. Check for issues that couldn't be auto-fixed
echo "  ├─ Checking for remaining issues..."

ISSUES_FOUND=0

# Check for any remaining underscore figure captions
if grep -q '^_Figure [0-9]\+:.*_$' "$TARGET_FILE"; then
    echo "    ⚠️  Some underscore figure captions couldn't be auto-fixed"
    ISSUES_FOUND=1
fi

# Check for improperly formatted alerts (alert type with content on same line)
if grep -q '^> \[![A-Z]*\] [^*]' "$TARGET_FILE"; then
    echo "    ⚠️  Some markdown alerts may need manual fixing"
    ISSUES_FOUND=1
fi

# 6. Show summary
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