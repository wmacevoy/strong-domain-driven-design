# redtry.sh CLASS WHAT FILE FROM TO: one edit (wherever the text stands) to the generator's model
# or the copier's tree of CLASS, then the kernel is asked again. Says which theorem refuses it.
c="$1"; what="$2"; file="$3"; from="$4"; to="$5"
rm -rf "$D"; mkdir -p "$D"; cp -r "$G/build" "$D/build"; cp "$G/gen/${c}Model.lean" "$G/gen/${c}Tree.lean" "$D/"
python3 - "$D/$file" "$from" "$to" <<'P'
import sys
p,a,b=sys.argv[1:]; s=open(p).read(); assert s.count(a)>=1,a; open(p,'w').write(s.replace(a,b))
P
cd "$D"
out=$( (LEAN_PATH=build "$L" -o "build/${c}Model.olean" "${c}Model.lean" && LEAN_PATH=build "$L" -o "build/${c}Tree.olean" "${c}Tree.lean") 2>&1 | grep "error" | head -1 | cut -c1-70)
line=$(echo "$out" | grep -o "Tree.lean:[0-9]*" | cut -d: -f2)
which=$( [ -n "$line" ] && awk -v n="$line" 'NR<=n && /^theorem /{t=$2} END{printf "%s", t}' "${c}Tree.lean")
if [ -n "$which" ]; then echo "red: $c: $what -> refused at $which"; else echo "red: $c: $what -> NOT CAUGHT ($out)"; fi
