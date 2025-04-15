from lean_sdk.schema import CommandResponse, Message, Sorry, TacticResponse
import re


def normalize_meta_vars(data: str):
    # Replace all occurrences of ?m.N with normalized numbers
    matches = re.finditer(r"\?m\.(\d+)", data)
    seen_numbers = {}

    # Build replacement mapping
    for match in matches:
        num = match.group(1)
        if num not in seen_numbers:
            seen_numbers[num] = str(len(seen_numbers) + 1)

    # Do the replacements
    for old_num, new_num in seen_numbers.items():
        data = data.replace(f"?m.{old_num}", f"?m.{new_num}")

    return data


def messages_equal(a: Message, b: Message):
    a.data = normalize_meta_vars(a.data)
    b.data = normalize_meta_vars(b.data)
    return (
        a.severity == b.severity
        and a.pos == b.pos
        and a.endPos == b.endPos
        and a.data == b.data
    )


def sorries_equal(a: Sorry, b: Sorry):
    a.goal = normalize_meta_vars(a.goal)
    b.goal = normalize_meta_vars(b.goal)
    return a.pos == b.pos and a.endPos == b.endPos and a.goal == b.goal


def command_responses_equal(a: CommandResponse, b: CommandResponse):
    return a.messages == b.messages and a.sorries == b.sorries


def tactic_responses_equal(a: TacticResponse, b: TacticResponse):
    return (
        a.goals == b.goals and a.sorries == b.sorries and a.proofStatus == b.proofStatus
    )


Sorry.__eq__ = sorries_equal
Message.__eq__ = messages_equal
CommandResponse.__eq__ = command_responses_equal
TacticResponse.__eq__ = tactic_responses_equal
