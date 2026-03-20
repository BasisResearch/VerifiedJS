#!/bin/bash
# Generate module dependency graph as JSON
cd /opt/verifiedjs
export ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH

echo "{"
echo "  \"modules\": ["

FIRST=true
for lean_file in $(find VerifiedJS/ -name "*.lean" | sort); do
  MODULE=$(echo "$lean_file" | sed "s|/|.|g" | sed "s|\.lean$||")
  DEPS=$(lake env lean --deps "$lean_file" 2>/dev/null | grep "/opt/verifiedjs/.lake/build/lib/lean/VerifiedJS/" | sed "s|.*/VerifiedJS/|VerifiedJS.|g" | sed "s|\.olean||g" | sed "s|/|.|g")
  
  # Check for sorry
  HAS_SORRY=false
  grep -q "sorry" "$lean_file" 2>/dev/null && HAS_SORRY=true
  
  # Count theorems
  THMS=$(grep -cE "^(private )?(theorem|lemma) " "$lean_file" 2>/dev/null || echo 0)
  LOC=$(wc -l < "$lean_file" 2>/dev/null || echo 0)
  
  if [ "$FIRST" = true ]; then FIRST=false; else echo ","; fi
  
  DEPS_JSON=$(echo "$DEPS" | grep -v "^$" | sed s/^//;s/$// | paste -sd, - 2>/dev/null || echo "")
  printf "    {\"name\": \"%s\", \"file\": \"%s\", \"deps\": [%s], \"sorry\": %s, \"theorems\": %d, \"loc\": %d}" \
    "$MODULE" "$lean_file" "$DEPS_JSON" "$HAS_SORRY" "$THMS" "$LOC"
done

echo ""
echo "  ]"
echo "}"
