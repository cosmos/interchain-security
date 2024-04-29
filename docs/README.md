# Website

This website is built using [Docusaurus 3](https://docusaurus.io/), a modern static website generator.

### Installation

```
$ npm install
```

### Local Development

```
$ npm run start
```

This command starts a local development server and opens up a browser window. Most changes are reflected live without having to restart the server.

### Build

```
$ npm run build
```

This command generates static content into the `build` directory and can be served using any static contents hosting service.

# Accessing versioned docs locally

```shell
# from interchain-security/docs run:
./sync_versions.sh
```

The script above will create `versioned_docs` and `versioned_sidebars` directories inside `interchain-security/docs`.

To view the docs run:

```shell
npm run start
```

Remember to check back out to your working branch. Running `./sync_versions.sh` will leave you in a detached head state.
(simply run `git checkout <working-branch>)


# Legacy documentation

`legacy-docs-page` [branch](https://github.com/cosmos/interchain-security/tree/legacy-docs-page) contains documentation for versions `<= v4.0.0`. These versions were built using docusaurus `v2.4.0` which is not compatible with docusaurus `v3.x` used at the time of writing. It was not feasible to port the legacy docs from `v2.4.0` because `v3.x` is not compatible with it and it required changing all release branches.

The `legacy` directory on `legacy-docs-page` was created manually, by modifying `docusaurus.config.js` and `versions.json` on `https://github.com/cosmos/interchain-security/releases/v3.3.1-lsm` and generating the static pages manually using `npm run build`.

The `legacy` directory gets included into the rest of the documentation using a simple `cp` command during the deploy process using the [build_deploy.sh](./build_deploy.sh) script. It is **not** included during local builds.
