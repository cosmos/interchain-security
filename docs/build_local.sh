#!/bin/sh

echo "building docusaurus from local branch"
npm ci && npm run build
echo "done building docusaurus from local docs"
