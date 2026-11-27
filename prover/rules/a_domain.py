"""
a domain  A program's parts are each a domain: a few directories, and of them the headers that are
          its ABI, the boundary; the rest is its inside, which only the domain uses. The program
          says them in a map: the file DOMAINS names, under SUBJECT (the rule is off without it):

              # a comment
              meetup  src/meetup src/strong/meetup | src/meetup/meetup.h src/meetup/ticket.h

          one line a domain: its name, its directories, `|`, its ABI headers. Or a domain laid out, with
          no `|`: its name is its namespace, and its first directory says the rest:

              Gosh::Meetup  src/meetup src/strong/meetup

          its ABI is the headers at the top of that directory; its inside, everything under it in
          imp/, and its other directories. A header at the top declares only into Gosh::Meetup, one
          under imp/ only into Gosh::Meetup::Imp, and nothing else declares into either: so the
          namespace is the domain, and says at every use which domain a name is of, and which side;
          and a name of Gosh::Meetup::Imp is used only in it. And a crossing that is
          there and is to go, one line each, so that the list can only shrink:

              allow src/pathfinding/finding.h meetup    # until meetup has an end

          a file that may still reach that domain's inside (or, for its own domain, an ABI header that
          may still name its inside): each such reach is said, every run, not refused; one that is not
          used any more is refused, so the line goes with it. And a domain named before it is laid out,
          `| *` for its ABI: every header in its directories, at any depth, that is of no deeper domain,
          as a program carries code it has not yet divided (a core around which a domain is laid out):

              core  src | *

          With RULES="a domain" this rule alone is run, and no other of the lint's, for a program held
          to its domains and nothing more: one around what is proved. Then, of every file
          under SUBJECT that is read:
            - a name declared in another domain is used only where that domain's ABI declares it,
              and only an ABI header of another domain is included;
            - what an ABI header declares (a function's parameters and result, a public field, a
              name for a type) names no type of its own domain's inside;
            - every source and header is of one domain, and an ABI header is of its own;
            - of a domain laid out, an ABI header declares only into NAME, a header under imp/ only
              into NAME::Imp, and no other domain's file into either (but main, and what has C's
              linkage, which are in no namespace by the language);
            - no header says `using namespace` outside a function: what it would bring in, it would
              bring into every file that includes it, and a crossing would be written with no name
              of where it goes.
          Refused otherwise. What is outside SUBJECT (the system's, INCLUDE's) is no domain's, and
          is used freely. It costs nothing when the program runs: the compiler is not asked to
          hide anything, and the boundary is read here, from Clang's tree.
"""
import os
import re

import clang.cindex as ci
from clang.cindex import CursorKind as K

USES = (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR, K.TYPE_REF, K.TEMPLATE_REF, K.CALL_EXPR, K.OVERLOADED_DECL_REF)
DECLARES = (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR, K.FIELD_DECL, K.TYPEDEF_DECL, K.TYPE_ALIAS_DECL, K.VAR_DECL)
# what a namespace may hold, by name: what is said of a laid-out domain's namespace is said of these
AT_NAMESPACE = (K.FUNCTION_DECL, K.VAR_DECL, K.TYPEDEF_DECL, K.TYPE_ALIAS_DECL, K.CLASS_DECL, K.STRUCT_DECL, K.UNION_DECL,
                K.ENUM_DECL, K.CLASS_TEMPLATE, K.FUNCTION_TEMPLATE, K.CLASS_TEMPLATE_PARTIAL_SPECIALIZATION)


INCLUDE = re.compile(r'^\s*#\s*include\s*"([^"]+)"', re.M)


ALL = "*"


def read_map(path):
    """([(name, [dir, ...], {abi header, ...} or None if laid out)], {(file, domain): line}), from the DOMAINS file;
    SystemExit if it is not there, or a line is not one."""
    if not os.path.isfile(path):
        raise SystemExit("lint: cannot start: DOMAINS names %s, which is not there" % path)
    domains, allows = [], {}
    for n, line in enumerate(open(path, encoding="utf-8"), 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("allow "):
            words = line.split()
            if len(words) != 3:
                raise SystemExit("lint: %s:%d: a crossing is `allow FILE DOMAIN`" % (path, n))
            allows[(words[1], words[2])] = n
            continue
        if "|" not in line:
            words = line.split()
            if len(words) < 2 or not re.match(r"^[A-Za-z_]\w*(::[A-Za-z_]\w*)*$", words[0]):
                raise SystemExit("lint: %s:%d: a domain laid out is `NAMESPACE DIR...`" % (path, n))
            domains.append((words[0], [w.rstrip("/") for w in words[1:]], None))
            continue
        if line.count("|") != 1:
            raise SystemExit("lint: %s:%d: a domain is `NAME DIR... | ABI-HEADER...`" % (path, n))
        left, right = line.split("|")
        words = left.split()
        if len(words) < 2:
            raise SystemExit("lint: %s:%d: a domain has a name and at least one directory" % (path, n))
        abi = right.split()
        # `| *`: every header in its directories (that is no deeper domain's) is of its ABI: a domain named, and
        # used as it is, before it is laid out
        domains.append((words[0], [w.rstrip("/") for w in words[1:]], ALL if abi == ["*"] else set(abi)))
    return domains, allows


class ADomain:
    def __init__(self, program, map_path):
        self.program = program
        self.map_name = os.path.relpath(map_path, program.subject_dir)
        domains, self.allows = read_map(map_path)
        self.laid = set(name for name, dirs, abi in domains if abi is None)
        self.domains = [(name, dirs, abi if abi is not None else self.top_headers(dirs[0])) for name, dirs, abi in domains]
        self.domains = [(name, dirs, self.all_headers(name, dirs) if abi == ALL else abi) for name, dirs, abi in self.domains]
        self.used = set()               # each allow that a reach was found for
        self.said = []
        self.refused = []
        self.seen = set()

    def top_headers(self, home):
        """A domain laid out: its ABI, the headers at the top of its first directory."""
        top = os.path.join(self.program.subject_dir, home)
        names = sorted(os.listdir(top)) if os.path.isdir(top) else []
        return set(home + "/" + f for f in names if f.endswith((".h", ".hpp")) and os.path.isfile(os.path.join(top, f)))

    def all_headers(self, name, dirs):
        """A domain of `| *`: every header in its directories, at any depth, that is of it and of no deeper domain."""
        found = set()
        for home in dirs:
            for root, _, names in os.walk(os.path.join(self.program.subject_dir, home)):
                for f in names:
                    if f.endswith((".h", ".hpp")):
                        rel = os.path.relpath(os.path.join(root, f), self.program.subject_dir)
                        if (self.domain_of(rel) or (None,))[0] == name:
                            found.add(rel)
        return found

    def rel(self, path):
        return os.path.relpath(os.path.realpath(path), self.program.subject_dir)

    def domain_of(self, rel):
        """The domain whose directory holds the file, the deepest if several; None if none."""
        best = None
        for name, dirs, abi in self.domains:
            for d in dirs:
                if (rel == d or rel.startswith(d + "/")) and (best is None or len(d) > len(best[1])):
                    best = (name, d, abi)
        return best

    def ours(self, path):
        return os.path.realpath(path).startswith(self.program.subject_dir)

    def check_files(self, paths, include_dirs):
        """Every source and header of the program is of a domain, and includes no other domain's inside; every ABI
        header is of its own, and there. The #include lines are read as they are written, each one: Clang's list
        has a header only where it was first read."""
        for path in paths:
            rel = self.rel(path)
            if self.domain_of(rel) is None:
                self.refused.append("%s: of no domain (%s says what each file is of)" % (rel, self.map_name))
            text = open(path, encoding="utf-8", errors="replace").read()
            for m in INCLUDE.finditer(text):
                for d in [os.path.dirname(path), self.program.subject] + include_dirs:
                    found = os.path.join(d, m.group(1))
                    if os.path.isfile(found):
                        self.see_include(path, found, text.count("\n", 0, m.start()) + 1)
                        break
        for name, dirs, abi in self.domains:
            for h in sorted(abi):
                if not os.path.isfile(os.path.join(self.program.subject_dir, h)):
                    self.refused.append("%s: %s's ABI names %s, which is not there" % (self.map_name, name, h))
                elif (self.domain_of(h) or (None,))[0] != name:
                    self.refused.append("%s: %s's ABI names %s, which is not in its directories" % (self.map_name, name, h))

    def see_include(self, source, included, line):
        """An #include of another domain's header that is not of its ABI."""
        if not (self.ours(source) and self.ours(included)):
            return
        here, there = self.domain_of(self.rel(source)), self.domain_of(self.rel(included))
        if here is None or there is None or here[0] == there[0] or self.rel(included) in there[2]:
            return
        self.found_one(source, there[0], "%s:%d: includes %s, of %s's inside" % (self.rel(source), line, self.rel(included), there[0]))

    def see(self, c, path):
        if c.kind in USES:
            self.use(c, path)
        elif c.kind in DECLARES:
            self.declare(c, path)
        if c.kind in AT_NAMESPACE:
            self.namespaced(c, path)
        elif c.kind == K.USING_DIRECTIVE and path.endswith((".h", ".hpp")) and self.ours(path):
            p = c.semantic_parent
            if p is None or p.kind in (K.NAMESPACE, K.TRANSLATION_UNIT):
                key = (path, c.location.line, "using")
                if key not in self.seen:
                    self.seen.add(key)
                    self.refused.append("%s:%d: a header says `using namespace` outside a function: it would be said in every file that "
                                        "includes it (%s)" % (self.rel(path), c.location.line, self.map_name))

    def namespaced(self, c, path):
        """Of a domain laid out: a header under imp/ declares only into NAME::Imp; an ABI header, nothing into it; no
        other domain's file, anything."""
        if c.semantic_parent is None or c.semantic_parent.kind not in (K.NAMESPACE, K.TRANSLATION_UNIT):
            return                                      # a member, a local: its class or function is what is placed
        if not c.location.file or os.path.realpath(c.location.file.name) != path:
            return
        if c.kind == K.FUNCTION_DECL and (c.spelling == "main" or (c.mangled_name and not c.mangled_name.startswith("_Z"))):
            return                                      # main, and what has C's linkage: in no namespace, by the language
        chain, p = [], c.semantic_parent
        while p is not None and p.kind == K.NAMESPACE:
            chain.insert(0, p.spelling)
            p = p.semantic_parent
        rel = self.rel(path)
        here = self.domain_of(rel)
        ns = "::".join(chain)
        into = None                                     # the laid-out domain whose namespace (or its Imp) this is in
        for name in self.laid:
            if ns == name or ns.startswith(name + "::"):
                if into is None or len(name) > len(into):
                    into = name
        inside_ns = into is not None and (ns == into + "::Imp" or ns.startswith(into + "::Imp::"))
        what = None
        mine = here is not None and here[0] in self.laid and rel.startswith(here[1] + "/") and rel.endswith((".h", ".hpp"))
        if mine and rel.startswith(here[1] + "/imp/"):
            if not (into == here[0] and inside_ns):
                what = "%s:%d: %s is of %s's inside (imp/), and is declared outside %s::Imp" % (rel, c.location.line, c.spelling, here[0], here[0])
        elif mine and rel in here[2]:
            if into == here[0] and inside_ns:
                what = "%s:%d: %s is declared into %s::Imp by an ABI header: the boundary is outside it" % (rel, c.location.line, c.spelling, into)
            elif into != here[0]:
                what = "%s:%d: %s is of %s's ABI, and is declared outside %s" % (rel, c.location.line, c.spelling, here[0], here[0])
        elif into is not None and (here is None or here[0] != into):
            what = "%s:%d: %s is declared into %s by a file of %s" % (rel, c.location.line, c.spelling, ns, here[0] if here else "no domain")
        if what is not None:
            key = (path, c.location.line, c.spelling)
            if key not in self.seen:
                self.seen.add(key)
                if here is not None and (rel, here[0]) in self.allows:
                    self.used.add((rel, here[0]))
                    self.said.append(what)
                else:
                    self.refused.append(what + " (%s)" % self.map_name)

    def use(self, c, path):
        d = c.referenced
        if d is None or d.location.file is None:
            return
        d = d.canonical                                 # where it is first declared: an ABI header, if it is one
        if d.location.file is None or not self.ours(d.location.file.name):
            return
        here, there = self.domain_of(self.rel(path)), self.domain_of(self.rel(d.location.file.name))
        if here is None or there is None or here[0] == there[0]:
            return
        if self.rel(d.location.file.name) in there[2]:
            return
        key = (path, c.location.line, d.spelling)
        if key in self.seen:
            return
        self.seen.add(key)
        self.found_one(path, there[0], "%s:%d: uses %s, of %s's inside (%s)"
                       % (self.rel(path), c.location.line, d.spelling, there[0], self.rel(d.location.file.name)))

    def found_one(self, path, domain, what):
        """A reach into another domain's inside: said, if the map allows that file that crossing; refused otherwise."""
        if (self.rel(path), domain) in self.allows:
            self.used.add((self.rel(path), domain))
            self.said.append(what)
        else:
            self.refused.append(what + ": another domain is used by its ABI (%s)" % self.map_name)

    def declare(self, c, path):
        """What an ABI header declares names no type of its own domain's inside."""
        here = self.domain_of(self.rel(path))
        if here is None or self.rel(path) not in here[2]:
            return
        if c.kind in (K.CXX_METHOD, K.CONSTRUCTOR, K.FIELD_DECL) and c.access_specifier == ci.AccessSpecifier.PRIVATE:
            return                                      # of the class's own inside: not on its boundary
        p = c.semantic_parent
        while p is not None and p.kind in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE, K.UNION_DECL):
            p = p.semantic_parent
        if p is not None and p.kind not in (K.NAMESPACE, K.TRANSLATION_UNIT):
            return                                      # a local, or what a function's body declares: its inside
        types = []
        if c.kind in (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR):
            types = [c.result_type] + [a.type for a in c.get_arguments()]
        elif c.kind in (K.TYPEDEF_DECL, K.TYPE_ALIAS_DECL):
            types = [c.underlying_typedef_type]
        else:
            types = [c.type]
        for t in types:
            for named in self.named(t):
                f = named.location.file
                if f is None or not self.ours(f.name):
                    continue
                rel = self.rel(f.name)
                there = self.domain_of(rel)
                if there is not None and there[0] == here[0] and rel not in here[2]:
                    key = (path, c.location.line, named.spelling)
                    if key not in self.seen:
                        self.seen.add(key)
                        what = "%s:%d: %s, of %s's ABI, names %s, of its inside (%s)" % (self.rel(path), c.location.line, c.spelling, here[0], named.spelling, rel)
                        if (self.rel(path), here[0]) in self.allows:
                            self.used.add((self.rel(path), here[0]))
                            self.said.append(what)
                        else:
                            self.refused.append(what + ": what a boundary declares is of the boundary (%s)" % self.map_name)

    def named(self, t):
        """The declarations of the classes and types a type is made of: pointed to, referred to, an array's, a template's arguments."""
        out, todo, seen = [], [t], set()
        while todo:
            t = todo.pop()
            if t is None or t.spelling in seen:
                continue
            seen.add(t.spelling)
            if t.kind in (ci.TypeKind.POINTER, ci.TypeKind.LVALUEREFERENCE, ci.TypeKind.RVALUEREFERENCE):
                todo.append(t.get_pointee())
                continue
            if t.kind in (ci.TypeKind.CONSTANTARRAY, ci.TypeKind.INCOMPLETEARRAY):
                todo.append(t.element_type)
                continue
            decl = t.get_declaration()
            if decl is not None and decl.kind != K.NO_DECL_FOUND:
                out.append(decl)
            for i in range(max(t.get_num_template_arguments(), 0)):
                todo.append(t.get_template_argument_type(i))
        return out

    def found(self):
        for (f, d), n in sorted(self.allows.items()):
            if (f, d) not in self.used:
                self.refused.append("%s:%d: allows %s to reach %s's inside, and it no longer does: the line goes" % (self.map_name, n, f, d))
        return sorted(set(self.refused)), {"crossings": sorted(set(self.said))}
