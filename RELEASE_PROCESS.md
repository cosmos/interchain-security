# Release Process

- [Release Process](#release-process)
  - [Changelog](#changelog)
    - [Creating a new release branch](#creating-a-new-release-branch)
    - [Cutting a new release](#cutting-a-new-release)
    - [Update the changelog on main](#update-the-changelog-on-main)
  - [Tagging Procedure](#tagging-procedure)


This document outlines the release process for Interchain Security (ICS).

For details on ICS releases, see [RELEASES.md](./RELEASES.md).

## Changelog

For PRs that are changing production code, please add a changelog entry in `.changelog` (for details, see [contributing guidelines](./CONTRIBUTING.md#changelog)). 

To manage and generate the changelog on ICS, we currently use [unclog](https://github.com/informalsystems/unclog). 
Read the [README.md](https://github.com/informalsystems/unclog#readme) in the unclog repo for instruction on how to install and use unclog.

### Creating a new release branch 

Unreleased changes are collected on `main` in `.changelog/unreleased/`. 
However, `.changelog/` on `main` contains also existing releases (e.g., `v3.2.0`).
Thus, when creating a new release branch (e.g., `release/v3.3.x`), the following steps are necessary:

- create a new release branch, e.g., `release/v3.3.x`
    ```bash 
    git checkout main
    git pull 
    git checkout -b release/v3.3.x
    ```
- delete all the sub-folders in `.changelog/` except `unreleased/` 
    ```bash
    find ./.changelog -mindepth 1 -maxdepth 1 -type d -not -name unreleased | xargs rm -r
    ```
- replace the content of `.changelog/epilogue.md` with the following text
    ```md
    ## Previous Versions

    [CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)
    ```
- push the release branch upstream 
    ```bash 
    git push
    ```

### Cutting a new release

Before cutting a _**release candidate**_ (e.g., `v3.3.0-rc0`), the following steps are necessary:

- move to the release branch, e.g., `release/v3.3.x`
    ```bash 
    git checkout release/v3.3.x
    ```
- move all entries in ".changelog/unreleased" to the release version, e.g., `v3.3.0`, i.e.,
    ```bash
    unclog release v3.3.0
    ```
- update `CHANGELOG.md`, i.e.,
    ```bash
    unclog build > CHANGELOG.md
    ```
- open a PR (from this new created branch) against the release branch, e.g., `release/v3.3.x`

Now you can cut the release candidate, e.g., v3.3.0-rc0 (follow the [Tagging Procedure](#tagging-procedure)).

### Update the changelog on main

Once the **final release** is cut, the new changelog section must be added to main:

- checkout a new branch from the `main` branch, i.e.,
    ```bash
    git checkout main
    git pull 
    git checkout -b <username>/backport_changelog
    ```
- bring the new changelog section from the release branch into this branch, e.g.,
    ```bash
    git checkout release/v3.3.x .changelog/v3.3.0
    ```
- remove duplicate entries that are both in `.changelog/unreleased/` and the new changelog section, e.g., `.changelog/v3.3.0`
- update `CHANGELOG.md`, i.e.,
    ```bash
    unclog build > CHANGELOG.md
    ```
- open a PR (from this new created branch) against `main`

## Tagging Procedure

**Important**: _**Always create tags from your local machine**_ since all release tags should be signed and annotated.

The following steps are the default for tagging a specific branch commit using git 
on your local machine. Usually, release branches are labeled `release/v*`:

Ensure you have checked out the commit you wish to tag and then do:
```bash
git pull --tags
git tag -s v3.2.0 -m v3.2.0
git push origin v3.2.0
```

To re-create a tag:
```bash
# delete a tag locally
git tag -d v3.2.0

# push the deletion to the remote
git push --delete origin v3.2.0

# redo the tagging
git tag -s v3.2.0 -m v3.2.0
git push origin v3.2.0
```

For final releases, once the tag is created, use the GitHub interface to create a release. 
Note that this is not necessary for release candidates.  