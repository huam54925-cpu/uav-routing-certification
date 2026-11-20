"""Finite-control, Boolean-stack transcription of the Lean fee suffix.

A dispatch is charged one transition, even when a branch performs a bounded
number of stack primitives inside the statement (as in TM2.stepAux).
"""


def run_tail(dim_bits, parent_body, n, suffix, context):
    def stack(wire):
        return list(reversed(wire))

    def take(tape):
        return tape.pop() if tape else None

    dimension = stack(dim_bits)
    parents = stack(parent_body)
    source = stack(suffix)
    saved_context = stack(context)
    tmp, expected, ticks, rev = [], [], [], []
    outputs = {f: [] for f in ("nums", "dens", "bnum", "bden")}
    state, field, end_ok = "dim_reverse", "nums", False
    limit = 4*len(parent_body) + 8*len(dim_bits) + 2*n + 3*len(suffix) + 64
    for steps in range(1, limit + 1):
        if state == "dim_reverse":
            bit = take(dimension)
            if bit is None:
                expected.append("0")
                state = "dim_emit"
            else:
                tmp.append(bit)
        elif state == "dim_emit":
            bit = take(tmp)
            if bit is None:
                state = "header"
            else:
                dimension.append(bit)
                expected.extend((bit, "1"))
        elif state == "header":
            bit = take(expected)
            if bit is None:
                state = "count"
            elif take(source) != bit:
                state = "bad"
        elif state == "count":
            bit = take(parents)
            if bit is None:
                state = "back"
            else:
                tmp.append(bit)
                if bit == "0":
                    ticks.append("1")
                else:
                    # Caller supplied a structurally valid, fully framed table.
                    tmp.append(parents.pop())
        elif state == "back":
            bit = take(tmp)
            if bit is None:
                state = "more"
            else:
                parents.append(bit)
        elif state == "more":
            if take(ticks) is None:
                state = "flush"
            elif field == "nums":
                state = "sign"
            else:
                end_ok, state = False, "marker"
        elif state in ("sign", "marker", "digit"):
            bit = take(source)
            if bit is None:
                state = "bad"
                continue
            rev.append(bit)
            if state == "sign":
                end_ok, state = bit == "0", "marker"
            elif state == "digit":
                end_ok, state = bit == "1", "marker"
            elif bit == "1":
                state = "digit"
            elif not end_ok:
                state = "bad"
            else:
                state = "more" if field in ("nums", "dens") else "flush"
        elif state == "flush":
            bit = take(rev)
            if bit is not None:
                outputs[field].append(bit)
            elif field == "nums":
                field, state = "dens", "dim_reverse"
            elif field == "dens":
                field, state = "bnum", "sign"
            elif field == "bnum":
                field, end_ok, state = "bden", False, "marker"
            else:
                state = "eof"
        elif state in ("bad", "eof"):
            if dimension != stack(dim_bits) or parents != stack(parent_body) or saved_context != stack(context):
                raise AssertionError("caller stack was changed")
            accepted = state == "eof" and not source
            bodies = tuple("".join(reversed(out)) for out in outputs.values()) if accepted else None
            return bodies, "".join(reversed(saved_context)), steps
        else:
            raise AssertionError(state)
    raise AssertionError(f"fee suffix exceeded its paper bound of {limit} transitions")
