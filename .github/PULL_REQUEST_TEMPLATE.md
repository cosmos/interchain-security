---
name: Pull request template
about: Template for interchain security templates
title: ''
labels: ''
assignees: ''

---


# Description

Please include a summary of the changes and the related issue. If the issue was ambiguous try to clarify it in this section.


# Linked issues

Closes: `#<issue>`


# Type of change

Please delete options that are not relevant.

- [ ] Non-breaking changes
- [ ] New feature (adding functionality)
- [ ] Breaking change (fix, feature or refactoring that changes existing functionality)
- [ ] Requires state migrations
- [ ] Proto files changes
- [ ] Updates in store keepers or store keys
- [ ] Changes in genesis (import/export)
- [ ] Testing
- [ ] Dependency management (updates dependencies, adds replace calls in go.mod, go mod tidy)
- [ ] Documentation updates


# How was the feature tested?

- [ ] Unit tests
- [ ] E2E tests
- [ ] Integration tests/simulation
- [ ] Custom difference tests


# Issues and further questions

Please write any concerns you may have about this feature (remove if not relevant).


# Other information


# Checklist:

Please delete options that are not relevant.

- [ ] Relevant issus are linked
- [ ] PR depends on other features: `#<issue>`
- [ ] Other PRs depend on this feature: `#<issue>`
- [ ] Tests are passing (`make test`)
- [ ] `make proto-gen` was run (for changes in `.proto` files)
- [ ] `make proto-lint` was run (for changes in `.proto` files)
- [ ] PR satisfies closing criteria defined in issue (remove if not applicable or issue has no criteria)
- [ ] Added iterators follow SDK pattern (`IterateX(ctx sdk.Context, cb func(arg1, arg2) (stop bool))`)
- [ ] testutil/e2e/debug_test.go is up-to-date with additional or changed e2e test names
- [ ] Documentation has been updated
