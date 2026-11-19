#!/bin/sh
# The spike, seen green and seen red (2026-11-18): Gauge's trees and models as they are, then the
# generator's model broken four ways and the copier's tree broken five. Each break must be refused
# by the kernel, at the theorem that is there for it.
#     LEAN=/path/to/lean PYTHON=python-with-libclang sh spike-tree/red.sh      (about a minute)
set -e
G=$(cd "$(dirname "$0")/.." && pwd); cd "$G"
: "${LEAN:=lean}" "${PYTHON:=python3}"
L=$LEAN; D=$(mktemp -d); export G L D LEAN_PATH=build
sh prove.sh Gauge >/dev/null
"$PYTHON" prooc.py spike-tree/Climb.hpp -o gen >/dev/null        # a class of the spike's own: its model, with no claims
"$LEAN" -o build/ClimbModel.olean gen/ClimbModel.lean
"$LEAN" -o build/Cxx.olean spike-tree/Cxx.lean
for c in model/Gauge.hpp spike-tree/Climb.hpp; do
    n=$(basename "$c" .hpp)
    "$PYTHON" spike-tree/tree.py "$c" -o gen >/dev/null
    "$LEAN" -o "build/${n}Tree.olean" "gen/${n}Tree.lean" 2>&1 | grep "error" && { echo "FAIL: as it is, the kernel refuses $n"; exit 1; }
    echo "as it is: $n: the kernel accepts $(grep -c '^theorem' "gen/${n}Tree.lean") theorems"
done
R="$G/spike-tree/redtry.sh"
{
sh "$R" Gauge "the generator writes >= for > in set's model" GaugeModel.lean "if (value > me.limit) then" "if (value ≥ me.limit) then"
sh "$R" Gauge "the generator forgets set's assignment of level" GaugeModel.lean "  me := { me with level := value }
  return (me, ())

def setLimit" "  return (me, ())

def setLimit"
sh "$R" Gauge "the generator's constructor gives limit 2" GaugeModel.lean "me := { me with limit := 1#32 }" "me := { me with limit := 2#32 }"
sh "$R" Gauge "the generator's invariant says <" GaugeModel.lean "(me.level ≤ me.limit)" "(me.level < me.limit)"
sh "$R" Gauge "the copier writes >= for > in set's tree" GaugeTree.lean '(Expr.cmp CmpOp.gt (Expr.name "value") (Expr.name "limit"))' '(Expr.cmp CmpOp.ge (Expr.name "value") (Expr.name "limit"))'
sh "$R" Gauge "the copier swaps two names in setLimit's tree" GaugeTree.lean '(Stmt.set "limit" (Expr.name "value"))' '(Stmt.set "level" (Expr.name "value"))'
sh "$R" Gauge "the copier converts a literal to 8 bits, not 32 (no words of its own)" GaugeTree.lean '(Expr.conv Ty.u32 (Expr.lit 1))' '(Expr.conv Ty.u8 (Expr.lit 1))'
sh "$R" Gauge "the copier drops a statement" GaugeTree.lean '(Stmt.seq (Stmt.set "limit" (Expr.name "value")) ' '(Stmt.seq Stmt.skip '
sh "$R" Gauge "the copier leaves out a conversion (an int assigned to a uint32_t field)" GaugeTree.lean '(Expr.conv Ty.u32 (Expr.lit 0))' '(Expr.lit 0)'
sh "$R" Climb "the generator's round steps i by 2" ClimbModel.lean "i := (i + 1#32)" "i := (i + 2#32)"
sh "$R" Climb "the generator's loop goes one round too far (<= for <)" ClimbModel.lean "if ¬ (i < n) then" "if ¬ (i ≤ n) then"
sh "$R" Climb "the generator returns n where k is returned, after a loop" ClimbModel.lean "  return (me, k)" "  return (me, n)"
sh "$R" Climb "the generator gives a loop no rounds at all" ClimbModel.lean "add.loop1 fuel fuel me n i" "add.loop1 fuel 0 me n i"
sh "$R" Climb "the generator's round forgets a statement of the loop's body" ClimbModel.lean "  me := { me with steps := (me.steps + 1#32) }
" ""
sh "$R" Climb "the copier writes - for + in the for's step" ClimbTree.lean '"i" (Expr.bin BinOp.add (Expr.name "i") (Expr.conv Ty.u32 (Expr.lit 1)))' '"i" (Expr.bin BinOp.sub (Expr.name "i") (Expr.conv Ty.u32 (Expr.lit 1)))'
sh "$R" Climb "the copier writes >= for > in the while's condition" ClimbTree.lean '(Expr.cmp CmpOp.gt (Expr.name "n") (Expr.name "total"))' '(Expr.cmp CmpOp.ge (Expr.name "n") (Expr.name "total"))'
sh "$R" Climb "the copier gives a local another type (uint8_t)" ClimbTree.lean '(Stmt.decl "uint32_t" "k"' '(Stmt.decl "uint8_t" "k"'
sh "$R" Climb "the copier drops a statement of a loop's body" ClimbTree.lean '(Stmt.seq (Stmt.set "n" (Expr.bin BinOp.sub (Expr.name "n") (Expr.conv Ty.u32 (Expr.lit 1)))) ' '(Stmt.seq Stmt.skip '
} | tee "$D.out"
if grep -q "NOT CAUGHT" "$D.out"; then echo "FAIL"; exit 1; fi
echo "PASS: $(grep -c 'refused at' "$D.out") breaks, each refused"
