# Challenge XXXX[^challenge_id]: Challenge Title

- **Status:** *One of the following: \[Open | Resolved | Expired\]*
- **Solution:** *Option field to point to the PR that solved this challenge.*
- **Tracking Issue:** *Link to issue*
- **Start date:** *YYYY/MM/DD*
- **End date:** *YYYY/MM/DD*
- **Reward:** *TBD*[^reward]

-------------------


## Goal

*Describe the goal of this challenge with 1-2 sentences.*

## Motivation

*Explain why this is a challenge that should be prioritized. Consider using a motivating example.*

## Description

*Describe the challenge in more details.*

### Assumptions

*Mention any assumption that users may make. Example, "assuming the usage of Stacked Borrows".*

### Success Criteria

*Here are some examples of possible criteria:*

All the following unsafe functions must be annotated with safety contracts and the contracts have been verified:

| Function | Location |
|---------|---------|
|  abc   |  def    |

At least N of the following usages were proven safe:

| Function | Location |
|---------|---------|
|  xyz   |  123   |

All proofs must automatically ensure the absence of the following undefined behaviors [ref](https://github.com/rust-lang/reference/blob/142b2ed77d33f37a9973772bd95e6144ed9dce43/src/behavior-considered-undefined.md):

*List of UBs*

Note: All solutions to verification challenges need to satisfy the criteria established in the [challenge book](general-rules.md)
in addition to the ones listed above.

[^challenge_id]: The number of the challenge sorted by publication date.
[^reward]: Leave it as TBD when creating a new challenge. This should only be filled by the reward committee.
