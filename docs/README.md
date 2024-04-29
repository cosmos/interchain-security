# Website

This website is built using [Docusaurus 3](https://docusaurus.io/), a modern static website generator.

### Installation

```
$ yarn
```

### Local Development

```
$ yarn start
```

This command starts a local development server and opens up a browser window. Most changes are reflected live without having to restart the server.

### Build

```
$ yarn build
```

This command generates static content into the `build` directory and can be served using any static contents hosting service.

### Deployment

Using SSH:

```
$ USE_SSH=true yarn deploy
```

Not using SSH:

```
$ GIT_USER=<Your GitHub username> yarn deploy
```

If you are using GitHub pages for hosting, this command is a convenient way to build the website and push to the `gh-pages` branch.


# Legacy documentation

`legacy` folder contains documentation for versions `<= v4.0.0`. These versions were using docusaurus `v2.4.0` which is not compatible with docusaurus `v3.x` used at the time of writing.

The folder was created manually, by modifying `docusaurus.config.js` and `versions.json` on `https://github.com/cosmos/interchain-security/tree/mmulji-ic/add-docs-versioning` and generating the static pages manually.

The `legacy` folder gets included into the rest of the documentation using a simple `cp` command during the deploy process using the [build_deploy.sh](./build_deploy.sh) script.
