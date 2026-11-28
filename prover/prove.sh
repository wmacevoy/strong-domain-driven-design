#!/bin/sh
# prove.sh CLASS...: generate what is owed from the C++, check the claims' proof of it, audit that
# proof as something untrusted, and compare the model with the C++.
# LEAN is the lean program (a release of Lean 4 unpacked anywhere; no packages are needed).
# DOMAIN is a directory with model/C.hpp and claims/CClaims.lean (and scripts/C.py, if any): this
# one, or another project's. gen/ and build/ are written there.
# A class of another program is read where it stands, with no text of it kept here: from/C is one
# line, the file's path under SUBJECT (that program's directory), and the class C of that file is
# read as it is today (or the function C, if the line's second word is "function"). Such a class may say no invariant: it cannot be changed from here.
# "class NAME" after the path: the class is called NAME where it stands (in its namespaces), and C is
# the name it is proved under here, so that two parts' classes of one name are two domains.
# READ_ONLY=1 stops after the generator has read each class and written gen/: what ingress.py and
# lint.py need, so that the program is looked over before anything is proved.
set -e
home=$(cd "$(dirname "$0")" && pwd)
cd "${DOMAIN:-$home}"
: "${LEAN:=lean}" "${PYTHON:=python3}" "${CXX:=c++}"
bin=$(dirname "$(command -v "$LEAN")")
PATH="$bin:$PATH"; export PATH          # the audit and leanchecker ask `lean` where its library is
mkdir -p build gen
export LEAN_PATH=build
if [ -z "$READ_ONLY" ]; then
    cp "$home/Prooc.lean" "$home/Audit.lean" build/      # lean reads only what is under the directory it runs in
    "$LEAN" -o build/Prooc.olean build/Prooc.lean
fi
before=""      # each domain proved so far in this run, NAME:CXXNAME:KIND: a proof file of a later one may use it
for c in "$@"; do
    kind=""; cname=""; used=""     # used: the compiled files of each class it uses, which its claims may import
    if [ -f "from/$c" ]; then
        : "${SUBJECT:?prove.sh: from/$c names a file of another program: set SUBJECT to its directory}"
        read -r rel kind cname < "from/$c"  # the file; "function" if C is one, not a class; or "class NAME"
        [ "$kind" = class ] || cname="$c"
        source="$SUBJECT/$rel"
        uses=""                             # further lines, "uses U": a class its methods take as a parameter, or it has as a part
        for u in $(sed -n 's/^uses //p' "from/$c"); do
            [ -n "$READ_ONLY" ] || [ -f "build/${u}Claims.olean" ] || { echo "FAIL: $c: it uses $u, which is not proved yet: name $u before it"; exit 1; }
            read -r urel _ < "from/$u"
            uses="$uses --uses $SUBJECT/$urel:$u"
            # and what it is read with, as its own from/ file says: its `only`, and where its methods are defined
            uonly=$(sed -n 's/^only //p' "from/$u" | tr ' ' ',')
            [ -z "$uonly" ] || uses="$uses --uses-option $u:only:$uonly"
            udef=$(sed -n 's/^defined //p' "from/$u")
            [ -z "$udef" ] || uses="$uses --uses-option $u:defined:$SUBJECT/$udef"
            used="$used build/${u}Model.olean build/${u}Owed.olean build/${u}Claims.olean"
        done
        rm -f "gen/$c.read.hpp"
        # and "needs REL NAME": a name for a type or a number that it is written with, from the file REL
        needs=$(sed -n 's|^needs \([^ ]*\) \([^ ]*\)$|--needs '"$SUBJECT"'/\1:\2|p' "from/$c")
        # and "outside NAME file FILE", "outside NAME reads|writes PARAM COUNT", "outside NAME gives LO HI":
        # a function outside the program, called by its contract (COUNT, LO, HI: a literal, a parameter, or PARAM-LIT)
        needs="$needs $(sed -n 's|^outside \([^ ]*\) file \([^ ]*\)$|--outside \1:file:'"$SUBJECT"'/\2|p; t; s|^outside \([^ ]*\) keeps \([^ ]*\)$|--outside \1:keeps:\2|p; t; s|^outside \([^ ]*\) \([^ ]*\) \([^ ]*\) *\([^ ]*\)$|--outside \1:\2:\3:\4|p' "from/$c")"
        # and "includes FILE": a header of that program it is written with, included whole: compiled, not read
        needs="$needs $(sed -n 's|^includes \([^ ]*\)$|--includes '"$SUBJECT"'/\1|p' "from/$c")"
        # and "defined FILE": a source file where its methods are defined, outside the class
        needs="$needs $(sed -n 's|^defined \([^ ]*\)$|--defined '"$SUBJECT"'/\1|p' "from/$c")"
        # and "only M1 M2 ...": of a class that says no invariant, these methods and no others
        needs="$needs $(sed -n 's|^only \(.*\)$|--only \1|p' "from/$c" | tr ' ' ',' | sed 's/^--only,/--only /')"
        # and "buffer FILE TYPE DATA LEN": a type of that program's, in FILE, that is bytes it owns, made from their number
        needs="$needs $(sed -n 's|^buffer \([^ ]*\) \([^ ]*\) \([^ ]*\) \([^ ]*\)$|--buffer '"$SUBJECT"'/\1:\2:\3:\4|p' "from/$c")"
        "$PYTHON" "$home/prooc.py" "$source" "--${kind:-class}" "$cname" --as "$c" $uses $needs --invariant-may-be-absent -o gen >/dev/null
    else
        source="model/$c.hpp"
        "$PYTHON" "$home/prooc.py" "$source" -o gen >/dev/null
    fi
    if [ -n "$READ_ONLY" ]; then echo "READ $c"; continue; fi
    "$LEAN" -o "build/${c}Model.olean" "gen/${c}Model.lean"
    "$LEAN" -o "build/${c}Owed.olean" "gen/${c}Owed.lean"
    # What is owed is now fixed. The claims are compiled after it, and may not change it: Lean runs
    # what a claims file says while it checks it, so the compiled files are compared before and after.
    # No claims yet: draft.py writes a first one, each statement tried by one automatic proof, and
    # `sorry` marked LEFT where it did not close (a person or an agent proves those).
    [ -f "claims/${c}Claims.lean" ] || "$PYTHON" "$home/draft.py" "$c"
    fixed=$(sha256sum build/Prooc.olean "build/${c}Model.olean" "build/${c}Owed.olean" $used)
    "$LEAN" -o "build/${c}Claims.olean" "claims/${c}Claims.lean" || { echo "FAIL: $c: a proof does not hold (claims/${c}Claims.lean)"; exit 1; }
    [ "$fixed" = "$(sha256sum build/Prooc.olean "build/${c}Model.olean" "build/${c}Owed.olean" $used)" ] || { echo "FAIL: $c: the claims changed what they are checked against"; exit 1; }
    left=$(grep -c -- '-- LEFT: the automatic proof' "claims/${c}Claims.lean" || true)
    [ "$left" = 0 ] || { echo "FAIL: $c: $left statements LEFT by draft.py in claims/${c}Claims.lean: prove them there"; exit 1; }
    "$LEAN" --run build/Audit.lean "$c" > "build/$c.audit" || { cat "build/$c.audit"; echo "FAIL: $c: the audit refused the claims (claims/${c}Claims.lean)"; exit 1; }
    "$bin/leanchecker" "${c}Claims" || { echo "FAIL: $c: Lean's kernel, asked again, does not accept the claims"; exit 1; }
    # "compared no REASON": a class that cannot be made here as the C++ makes it (its constructor is
    # not read): the model is not set beside the C++, and what is proved says so, and why.
    uncompared=$( [ -f "from/$c" ] && sed -n 's/^compared no //p' "from/$c" || true)
    if [ -z "$uncompared" ]; then
    cp "gen/$c.script" "build/$c.script"       # seeded calls; and a class's own, if it has them
    if [ -f "scripts/$c.py" ]; then "$PYTHON" "scripts/$c.py" >> "build/$c.script"; fi
    "$LEAN" --run "gen/${c}Diff.lean" < "build/$c.script" > "build/$c.model.out"
    "$CXX" -std=c++20 -Wall -Wextra -Werror -DPROOC_CHECKED -Imodel -Igen -I"$home/model" -o "build/${c}_diff" "gen/${c}_diff.cpp"
    "build/${c}_diff" < "build/$c.script" > "build/$c.cpp.out"
    cmp "build/$c.model.out" "build/$c.cpp.out" || { echo "FAIL: $c: the model and the C++ differ"; exit 1; }
    if grep -q "MEMORY ERROR\|should not have\|inv=0" "build/$c.model.out"; then echo "FAIL: $c: the model stopped, or the invariant did not hold: $(grep -m1 'MEMORY ERROR\|should not have\|inv=0' "build/$c.model.out")"; exit 1; fi
    fi
    {   # the product: what was proven, of exactly which text, by what, resting on what
        echo "class $c"; "$LEAN" --version
        (cd "$home" && sha256sum prooc.py cxx.py reader.py model.py cxxtypes.py owed.py compare.py subject.py clang_edge.py Prooc.lean Audit.lean model/Bytes.hpp)
        if [ -f "from/$c" ]; then
            if [ -n "$SUBJECT_COMMIT" ]; then at="$SUBJECT_COMMIT"      # SUBJECT is that commit's files, put there by the caller
            else at="$(git -C "$SUBJECT" rev-parse HEAD 2>/dev/null || echo 'no commit known')$(git -C "$SUBJECT" diff --quiet -- "$rel" 2>/dev/null || echo ', and changed since')"; fi
            echo "read from $rel, as it stands at $at"
            sha256sum "gen/$c.subject.hpp"
            if [ -f "gen/$c.read.hpp" ]; then echo "read with each pre(...) written again at the head of its method's body:"; sha256sum "gen/$c.read.hpp"; fi
        fi
        sha256sum "$source" "gen/${c}Model.lean" "gen/${c}Owed.lean" "claims/${c}Claims.lean"
        cat "build/$c.audit"
        echo "the kernel, asked again (leanchecker): accepted"
    } > "build/$c.bundle"
    if grep -q "says NO INVARIANT" "gen/${c}Model.lean"; then inv="; the class says no invariant"; else inv=", the invariant among them"; fi
    if [ -n "$uncompared" ]; then echo "PROVED $c: $(grep -c '^  [A-Za-z_]* : ' "gen/${c}Owed.lean") statements$inv; NOT COMPARED with the C++: $uncompared"; echo "not compared with the C++: $uncompared" >> "build/$c.bundle"
    else echo "PROVED $c: $(grep -c '^  [A-Za-z_]* : ' "gen/${c}Owed.lean") statements; model and C++ agree on $(wc -l < "build/$c.cpp.out") lines$inv"; fi
    "$PYTHON" "$home/review.py" "$c" || echo "REVIEW $c: not made (review.py failed): read the invariant by hand"
    # What is claimed of the class as a test that cannot be run (proofs/C.proof.cpp; model/forall.h says how
    # it is read): compiled as the C++ it is, made what is owed by proofs.py, and proved and audited as above.
    if [ -f "proofs/$c.proof.cpp" ]; then
        "$CXX" -std=c++17 -fsyntax-only -Wall -Wextra -Werror -Imodel -I"$home/model" ${SUBJECT:+-I"$SUBJECT"} "proofs/$c.proof.cpp" || { echo "FAIL: $c: proofs/$c.proof.cpp does not compile"; exit 1; }
        withs=""; for w in $before; do withs="$withs --with $w"; done
        [ "$kind" != function ] || withs="$withs --with $c:${cname:-$c}:function"    # a function's own file calls it
        "$PYTHON" "$home/proofs.py" "proofs/$c.proof.cpp" --class "$c" --named "${cname:-$c}" $withs -Imodel -I"$home/model" ${SUBJECT:+-I"$SUBJECT"} -o gen >/dev/null || { echo "FAIL: $c: proofs/$c.proof.cpp is not read"; exit 1; }
        # the models of the domains beside it that the file uses, which the claims may not change either
        beside=$(sed -n 's/^import \(.*\)Model$/build\/\1Model.olean/p' "gen/${c}ProofOwed.lean" | grep -v "^build/${c}Model.olean$" || true)
        # Run small (model/forall.h, PROOC_RUN), once proofs.py has read it (what it does not know is
        # refused first, not run): the same file as a test that runs, at its loops' edges and a seeded
        # sample, with the byte view checked and under the sanitizers. A claim that is false fails here
        # in a second, before Lean; and what proofs.py made of the file is set against a run of it.
        "$CXX" -std=c++17 -O1 -g -DPROOC_RUN -DPROOC_CHECKED -fsanitize=address,undefined -fno-sanitize-recover=all -Imodel -I"$home/model" ${SUBJECT:+-I"$SUBJECT"} "proofs/$c.proof.cpp" -o "build/${c}_run" || { echo "FAIL: $c: proofs/$c.proof.cpp does not compile to run"; exit 1; }
        ran=$(ASAN_OPTIONS=detect_leaks=0 "build/${c}_run" 2>&1) || { echo "$ran" | tail -n 8; echo "FAIL: $c: a PROVE of proofs/$c.proof.cpp is not proved: run at small bounds, it is false, or the run committed a memory error"; exit 1; }
        echo "RAN $c, proofs/$c.proof.cpp at small bounds: $ran (a test: it proves nothing)"
        "$LEAN" -o "build/${c}ProofOwed.olean" "gen/${c}ProofOwed.lean"
        fixed=$(sha256sum build/Prooc.olean "build/${c}Model.olean" $beside "build/${c}ProofOwed.olean")
        "$LEAN" -o "build/${c}ProofClaims.olean" "claims/${c}ProofClaims.lean" || { echo "FAIL: $c: a PROVE of proofs/$c.proof.cpp is not proved (claims/${c}ProofClaims.lean)"; exit 1; }
        [ "$fixed" = "$(sha256sum build/Prooc.olean "build/${c}Model.olean" $beside "build/${c}ProofOwed.olean")" ] || { echo "FAIL: $c: the claims changed what they are checked against"; exit 1; }
        "$LEAN" --run build/Audit.lean "${c}Proof" > "build/${c}Proof.audit" || { cat "build/${c}Proof.audit"; echo "FAIL: $c: the audit refused the claims (claims/${c}ProofClaims.lean)"; exit 1; }
        "$bin/leanchecker" "${c}ProofClaims" || { echo "FAIL: $c: Lean's kernel, asked again, does not accept the claims of its proofs"; exit 1; }
        {   echo "and of the same class: what proofs/$c.proof.cpp claims"
            sha256sum "proofs/$c.proof.cpp" "gen/${c}ProofOwed.lean" "claims/${c}ProofClaims.lean"; (cd "$home" && sha256sum proofs.py proofs_reader.py model/forall.h)
            cat "build/${c}Proof.audit"
        } >> "build/$c.bundle"
        echo "PROVED $c, as proofs/$c.proof.cpp says it: $(grep -c 'PROVE(' "proofs/$c.proof.cpp") PROVEs in $(grep -c '^PROOF(' "proofs/$c.proof.cpp") proofs, every round of every loop"
    fi
    before="$before $c:${cname:-$c}:${kind:-class}"
done
