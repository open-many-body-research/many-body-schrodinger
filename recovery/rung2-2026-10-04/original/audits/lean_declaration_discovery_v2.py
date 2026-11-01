"""Conservative declaration discovery for the audited continuation source form.

Supports one explicit namespace, public ASCII theorem/def/abbrev names (including
apostrophes), noncomputable/protected modifiers and balanced attributes. Comments
and literal contents are blanked without changing offsets or line positions.
Version 2 also recognizes the exact pinned Mathlib infinite-sum/product tokens
∑' and ∏', without blanking text or changing offsets.
This is not a general Lean parser. Unsupported potentially declaration-bearing
forms fail closed; the Lean compiler remains the authority on source validity.
"""
import re


def mask_lean_literals_and_comments(source):
    chars = list(source)
    n = len(source)

    def blank(lo, hi):
        for k in range(lo, hi):
            if chars[k] != "\n":
                chars[k] = " "

    i = 0
    while i < n:
        if source.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Lean block comment")
            blank(start, i)
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = n if end < 0 else end
            blank(i, end)
            i = end
        elif source[i] in "«»`":
            raise ValueError("quoted identifiers or syntax/name quotations are unsupported")
        elif re.match(r'[A-Za-z_][A-Za-z0-9_]*!"', source[i:]):
            raise ValueError("interpolated/custom string syntax is unsupported")
        elif source[i] == "r" and (i == 0 or not (source[i-1].isalnum() or source[i-1] in "_'")) \
                and (raw := re.match(r'r(#+)?"', source[i:])):
            start = i
            marker = '"' + (raw.group(1) or "")
            i += len(raw.group(0))
            end = source.find(marker, i)
            if end < 0:
                raise ValueError("unterminated Lean raw string")
            i = end + len(marker)
            blank(start, i)
        elif source[i] == '"':
            start = i
            i += 1
            while i < n and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            if i >= n:
                raise ValueError("unterminated Lean string")
            i += 1
            blank(start, i)
        elif source.startswith(("∑'", "∏'"), i):
            # Exact tokens from Mathlib/Topology/Algebra/InfiniteSum/Defs.lean.
            # Preserve both characters; inspect everything following the token.
            if i + 2 < n and source[i + 2] == "'":
                raise ValueError("unsupported repeated prime after infinite sum/product token")
            i += 2
        elif source[i] == "'" and (i == 0 or not (source[i-1].isalnum() or source[i-1] in "_'")):
            # Lean character literals; a prime appended to an identifier is not one.
            literal = re.match(r"'(?:[^'\\\n]|\\(?:[nrt0\\'\"]|x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}))'", source[i:])
            if not literal:
                raise ValueError("unsupported apostrophe/character-literal syntax")
            end = i + len(literal.group(0))
            blank(i, end)
            i = end
        else:
            i += 1
    return "".join(chars)


def discover_declarations(source):
    masked = mask_lean_literals_and_comments(source)
    chars = list(masked)
    # Attributes can share a line with a declaration or precede it on another line.
    i = 0
    while i < len(masked):
        if masked.startswith("@[", i):
            start, depth = i, 1
            i += 2
            while i < len(masked) and depth:
                if masked[i] == "[":
                    depth += 1
                elif masked[i] == "]":
                    depth -= 1
                i += 1
            if depth:
                raise ValueError("unterminated Lean attribute")
            for k in range(start, i):
                if chars[k] != "\n":
                    chars[k] = " "
        else:
            i += 1
    cleaned = "".join(chars)
    unsupported = re.search(
        r"^[ \t]*(?:(?:private|public|protected|noncomputable|unsafe|partial|nonrec|meta|local|scoped)[ \t]+)*"
        r"(?:axiom|opaque|constant|constants|instance|structure|class|inductive|coinductive|"
        r"syntax|macro|macro_rules|elab|elab_rules|run_elab|run_cmd|initialize|builtin_initialize|mutual|"
        r"notation|infix|infixl|infixr|prefix|postfix)\b", cleaned, re.M)
    if unsupported:
        line = source.count("\n", 0, unsupported.start()) + 1
        raise ValueError(f"unsupported declaration-bearing command at source line {line}")
    stack, scopes, namespace_tokens = [], [], []
    offset = 0
    for line in cleaned.splitlines(keepends=True):
        opening = re.match(r"^[ \t]*namespace\b(.*)$", line)
        section = re.match(r"^[ \t]*(?:noncomputable[ \t]+)?section(?:[ \t]+([A-Za-z][A-Za-z0-9_']*))?[ \t]*$", line)
        ending = re.match(r"^[ \t]*end(?:[ \t]+([A-Za-z][A-Za-z0-9_.']*))?[ \t]*$", line)
        if opening:
            name = opening.group(1).strip()
            if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*", name):
                raise ValueError("unsupported namespace name")
            namespace_tokens.append(offset + line.index("namespace"))
            stack.append(("namespace", name, offset))
        elif section:
            stack.append(("section", section.group(1), offset))
        elif ending:
            if not stack:
                raise ValueError("unmatched end command")
            kind, name, start = stack.pop()
            if ending.group(1) is not None and ending.group(1) != name:
                raise ValueError("unsupported or mismatched named end command")
            if kind == "namespace":
                scopes.append((name, start, offset))
        offset += len(line)
    all_namespace_tokens = [m.start() for m in re.finditer(r"(?<![\w'.])namespace(?![\w'.])", cleaned)]
    if (len(namespace_tokens) != 1 or all_namespace_tokens != namespace_tokens or len(scopes) != 1
            or any(kind == "namespace" for kind, _, _ in stack)):
        raise ValueError("exactly one explicitly closed namespace is supported")
    namespace, scope_start, scope_end = scopes[0]
    pattern = re.compile(
        r"^[ \t]*(?:(?:noncomputable|protected)[ \t]+)*(theorem|def|abbrev)[ \t]+"
        r"([A-Za-z][A-Za-z0-9_'.]*)(?=[\s(:{\[])", re.M)
    found = list(pattern.finditer(cleaned))
    if any(not (scope_start < m.start(1) < scope_end) for m in found):
        raise ValueError("declaration outside the supported namespace scope")
    keyword = re.compile(r"(?<![\w'.])(?:theorem|def|abbrev)(?![\w'.])")
    recognized = {m.start(1) for m in found}
    unrecognized = [m.start() for m in keyword.finditer(cleaned) if m.start() not in recognized]
    if unrecognized:
        lines = [source.count("\n", 0, p) + 1 for p in unrecognized]
        raise ValueError(f"unsupported declaration context/name at source lines {lines}")
    names = [m.group(2) for m in found]
    if any(name.startswith("_root_.") or ".." in name or name.endswith(".") for name in names):
        raise ValueError("absolute/invalid declaration names are unsupported")
    if len(set(names)) != len(names):
        raise ValueError("duplicate local declaration names require a fuller namespace parser")
    if not names:
        raise ValueError("no supported local declarations discovered")
    return namespace, names
