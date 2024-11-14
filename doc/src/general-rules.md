# General Rules

## Terms / Concepts

**Verification Target:** [Our repository](https://github.com/model-checking/verify-rust-std) is a fork of the original Rust repository,
and we kept a copy of the Rust standard library inside the `library/` folder that shall be used as the verification target for all our challenges.
We will periodically update the `library/` folder to track newer versions of the [official Rust standard library](https://github.com/rust-lang/rust/).

**NOTE:** This work is not officially affiliated, or endorsed by the Rust project or Rust Foundation.

**Challenges:** Each individual verification effort will have a
tracking issue where contributors can add comments and ask clarification questions.
You can find the list of [open challenges here](https://github.com/model-checking/verify-rust-std/labels/Challenge).

**Solutions:** Solutions to a problem should be submitted as a single Pull Request (PR) to this repository.
The solution should run as part of the CI.
See more details about [minimum requirements for each solution](general-rules.md#solution-requirements).


## Basic Workflow

1. A verification effort will be published in the repository with
appropriate details, and a tracking issue labeled with “Challenge”
will be opened, so it can be used for clarifications and questions, as
well as to track the status of the challenge.

2. Participants should create a fork of the repository where they will implement their proposed solution.
3. Once they submit their solution for analysis, participants should create a PR against the repository for analysis.
   Please make sure your solution meets [the minimum requirements described here](general-rules.md#solution-requirements).
4. Each contribution will be reviewed on a first come, first served basis.
   Acceptance will be based on a review by a committee.
5. Once approved by the review committee, the change will be merged into the repository.

## Solution Requirements

A proposed solution to a verification problem will only **be reviewed** if all the minimum requirements below are met:

* Each contribution or attempt should be submitted via a pull request to be analyzed by reviewers.
* By submitting the solution, participants confirm that they can use, modify, copy, and redistribute their contribution,
  under the terms of their choice.
* The contribution must be automated and should be checked and pass as part of the PR checks.
* All tools used by the solution must be in [the list of accepted tools](tools.md#approved-tools),
  and previously integrated in the repository.
  If that is not the case, please submit a separate [tool application first](./general-rules.md#tool-applications).
* There is no restriction on the number of contributors for a solution.
  Make sure you have the rights to submit your solution and that all contributors are properly mentioned.
* The solution cannot impact the runtime logic of the standard library unless the change is proposed and incorporated
  into the Rust standard library.

Any exception to these requirements will only be considered if it is specified as part of the acceptance criteria of the
challenged being solved.

## Call for Challenges

The goal of the effort is to enable the verification of the entire Rust standard library.
The type of obstacles users face may depend on which part of the standard library you would like to verify. Thus, our challenges are developed with the target of verifying a specific section of the standard library or strengthening existing verification.

Everyone is welcome to submit new challenge proposals for review by our committee.
Follow the following steps to create a new proposal:

1. Create a tracking issue using the [challenge template](./challenge_template.md) for your challenge.
2. In your fork of this repository do the following:
    1. Copy the template file (`book/src/challenge_template.md`) to `book/src/challenges/<ID_NUMBER>-<challenge-name>.md`.
    2. Fill in the details according to the template instructions.
    3. Add a link to the new challenge inside `book/src/SUMMARY.md`
    4. Submit a pull request.
3. Address any feedback in the pull request.
4. If approved, we will publish your challenge and add the “Challenge” label to the tracking issue.

## Tool Applications

Solutions must be automated using one of the tools previously approved and listed [here](tools.md#approved-tools):

* Any new tool that participants want to enable will require an application using the [tool application template](./tool_template.md).
* The tool will be analyzed by an independent committee consisting of members from the Rust open-source developers and AWS
* A new tool application should clearly specify the differences to existing techniques and provide sufficient background
  of why this is needed.
* The tool application should also include mechanisms to audit its implementation and correctness.
* Once the tool is approved, the participant needs to create a PR that creates a new action that runs the
  std library verification using the new tool, as well as an entry to the “Approved Tools” section of this book.
* Once the PR is merged, the tool is considered integrated.
* The repository will be updated periodically, which can impact the tool capacity to analyze the new version of the repository.
  I.e., the action may no longer pass after an update.
  This will not impact the approval status of the tool, however,
  new solutions that want to employ the tool may need to ensure the action is passing first.

## Committee Applications

You can apply to be part of the committee by submitting a pull request that adds your GitHub login name to the `pull_request.toml` file.

For example, if your user login is @rahulku, add the login without @ to the committee member's list,
```
[committee]
members = [
+   "rahulku"
]
```
