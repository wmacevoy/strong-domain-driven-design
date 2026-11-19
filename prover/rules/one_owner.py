"""
one owner  An object is used by one thread at a time, and objects apart by as many threads as
           is useful. That holds if no two objects share state that is written: so there is no
           global, no static in a function and no static member that can be written, but one
           that is each thread's own (`thread_local`) or made for many threads (`std::atomic`).
           Refused of what is under STRONG. Of anything else each one is said; and where there
           is one, starting a thread (std::thread, std::jthread, std::async, pthread_create)
           is refused. Where a thread is started and there is none, each start is said: that
           what it is handed is its alone is read by a person. A signal handler that is a
           function is said, each one: it runs between any two steps of its thread.

Threads and signal handlers are looked for by the words (see_text), in every file; what is shared by
Clang's reading (see).
"""
import os
import re

import clang.cindex as ci
from clang.cindex import CursorKind as K, TypeKind as TK

from .names import line_at

THREADS = r"\bstd\s*::\s*(?:thread|jthread|async)\b|\bpthread_create\b"


class OneOwner:
    def __init__(self, program):
        self.program = program
        self.refused = []
        self.shared = []
        self.threads = []
        self.handlers = []
        self.seen = set()

    def see_text(self, path, plain_text):
        """The words of one file, with comments and what is in quotes blanked (names.plain)."""
        rel = os.path.relpath(path, self.program.subject)
        for i, line in enumerate(plain_text.split("\n")):
            if re.search(THREADS, line):
                self.threads.append("%s:%d: %s" % (rel, i + 1, line_at(path, i + 1)[:150]))
            m = re.search(r"\bsignal\s*\(\s*[^,()]+,\s*([A-Za-z_]\w*)\s*\)", line)
            if (m and m.group(1) not in ("SIG_IGN", "SIG_DFL")) or re.search(r"\bsigaction\s*\(", line):
                self.handlers.append("%s:%d: %s" % (rel, i + 1, line_at(path, i + 1)[:150]))

    def see(self, c, path):
        if c.kind == K.VAR_DECL and (c.storage_class == ci.StorageClass.STATIC or c.semantic_parent.kind in (K.TRANSLATION_UNIT, K.NAMESPACE)
                                     or (c.semantic_parent.kind in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE))):
            t = c.type.get_canonical()
            fixed = t.is_const_qualified()
            while t.kind in (TK.CONSTANTARRAY, TK.INCOMPLETEARRAY):
                t = t.get_array_element_type().get_canonical()
                fixed = fixed or t.is_const_qualified()
            own = c.tls_kind != ci.TLSKind.NONE or "atomic" in c.type.spelling or "atomic" in t.spelling
            if not fixed and t.kind != TK.LVALUEREFERENCE and not own and (c.get_usr(), "shared") not in self.seen:
                self.seen.add((c.get_usr(), "shared"))
                rel, line = self.program.at(c)
                text = "%s:%d: `%s` can be written and is one for every object and every thread:\n    %s" % (rel, line, c.spelling, line_at(path, line)[:150])
                (self.refused if path.startswith(self.program.strong_dir) else self.shared).append(text)

    def found(self):
        refused = list(self.refused)
        if self.threads and self.shared:
            for x in self.threads:
                refused.append("%s\n    a thread is started, and there is state that can be written and is one for every thread (%d: the first is %s)"
                               % (x, len(set(self.shared)), sorted(set(self.shared))[0].split(": ")[0]))
        return refused, {"shared": sorted(set(self.shared)), "threads": self.threads, "handlers": self.handlers}
