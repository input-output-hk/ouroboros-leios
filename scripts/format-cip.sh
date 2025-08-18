#!/bin/bash

# CIP Auto-Formatter
# Generates TOC, table of figures/tables, and formats markdown

set -euo pipefail

TARGET_FILE="${1:-docs/cip/README.md}"

if [[ ! -f "$TARGET_FILE" ]]; then
    echo "❌ File $TARGET_FILE not found"
    exit 1
fi

echo "🔧 Formatting CIP document: $TARGET_FILE"

# Make backup
cp "$TARGET_FILE" "${TARGET_FILE}.bak"

# 1. Remove trailing periods from figure and table captions
echo "  ├─ Cleaning figure and table captions..."

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
    in_abstract = False
    
    for line in lines:
        # Check if we're entering or leaving the Abstract section
        if re.match(r'^##\s+Abstract\s*$', line.strip()):
            in_abstract = True
            continue
        elif re.match(r'^##\s+', line.strip()) and in_abstract:
            in_abstract = False
        
        # Match headers (## to ####)
        match = re.match(r'^(#{2,4})\s+(.+)$', line.strip())
        if match:
            level = len(match.group(1))
            title = match.group(2).strip()
            
            # Skip organizational headers that shouldn't be in main TOC
            skip_titles = ['figures', 'tables', 'table of contents', 'table of figures and tables']
            if title.lower() in skip_titles:
                continue
            
            # Skip figures and tables under Abstract
            if in_abstract and ('figure' in title.lower() or 'table' in title.lower()):
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

# 3. Generate table of figures and tables
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

def check_enumeration(items, item_type):
    """Check if figures/tables are correctly enumerated"""
    numbers = []
    for item in items:
        match = re.search(rf'{item_type} (\d+):', item)
        if match:
            numbers.append(int(match.group(1)))
    
    if not numbers:
        return True, []
    
    numbers.sort()
    expected = list(range(1, len(numbers) + 1))
    missing = []
    duplicates = []
    
    # Check for missing numbers
    for expected_num in expected:
        if expected_num not in numbers:
            missing.append(expected_num)
    
    # Check for duplicates
    seen = set()
    for num in numbers:
        if num in seen:
            duplicates.append(num)
        seen.add(num)
    
    is_correct = len(missing) == 0 and len(duplicates) == 0 and numbers == expected
    issues = missing + duplicates
    
    return is_correct, issues

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
        # Remove LaTeX formulas for cleaner table of figures
        caption = re.sub(r'\$[^$]+\$', '', caption)
        # Clean up extra spaces after formula removal
        caption = re.sub(r'\s+', ' ', caption).strip()
        anchor = generate_anchor_from_figure(caption)
        if anchor:
            figures.append(f"- [{caption}](#{anchor})")
    
    # Find all table captions (including multi-line)
    table_pattern = r'<em>(Table \d+: [^<]+)</em>'
    table_matches = re.findall(table_pattern, content, re.DOTALL)
    
    for match in table_matches:
        caption = match.strip()
        # Remove line breaks and normalize whitespace
        caption = re.sub(r'\s+', ' ', caption).strip()
        # Remove LaTeX formulas for cleaner table of figures
        caption = re.sub(r'\$[^$]+\$', '', caption)
        # Clean up extra spaces after formula removal
        caption = re.sub(r'\s+', ' ', caption).strip()
        # Extract table number for anchor
        table_num_match = re.search(r'Table (\d+)', caption)
        if table_num_match:
            anchor = f"table-{table_num_match.group(1)}"
            tables.append(f"- [{caption}](#{anchor})")
    
    # Check enumeration
    fig_correct, fig_issues = check_enumeration(figures, 'Figure')
    table_correct, table_issues = check_enumeration(tables, 'Table')
    
    if not fig_correct:
        print(f"⚠️  Figure enumeration issues: {fig_issues}", file=sys.stderr)
    if not table_correct:
        print(f"⚠️  Table enumeration issues: {table_issues}", file=sys.stderr)
    
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

# 4. Format markdown with prettier (max column length)
echo "  ├─ Formatting markdown with prettier..."

# Check if prettier is available, if not install it
if ! command -v prettier &> /dev/null; then
    echo "    Installing prettier..."
    npm install -g prettier
fi

# Format with prettier using max column width
prettier --write --prose-wrap always --print-width 80 "$TARGET_FILE"

# 5. Fix markdown alerts that prettier may have broken
echo "  ├─ Fixing markdown alert formatting..."

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

# 6. Show summary
echo "  └─ Formatting complete"

echo "✅ CIP formatted successfully"
rm -f "${TARGET_FILE}.bak"
