package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io/ioutil"
	"log"
	"os"
	"path/filepath"
	"strings"
)

func main() {
	// Define the directory to traverse and the output markdown file
	dir := "../../tests/integration"
	outputFile := "test_documentation.md"

	// Open the output file
	out, err := os.Create(outputFile)
	if err != nil {
		log.Fatalf("Error creating output file: %v\n", err)
	}
	defer out.Close()

	// Write the header for the markdown file
	fmt.Fprintf(out, "# Test Documentation\n\n")
	fmt.Fprintf(out, "| File | Function | Short Description |\n")
	fmt.Fprintf(out, "|------|----------|-------------------|\n")

	// Walk through the directory
	err = filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		// Only process .go files
		if !info.IsDir() && strings.HasSuffix(info.Name(), ".go") {
			extractDocstrings(path, out)
		}
		return nil
	})
	if err != nil {
		log.Fatalf("Error walking the path %q: %v\n", dir, err)
	}

	fmt.Printf("Documentation generated successfully in %s\n", outputFile)
}

func extractDocstrings(filePath string, out *os.File) {
	// Read the Go source file
	src, err := ioutil.ReadFile(filePath)
	if err != nil {
		log.Fatalf("Error reading file %s: %v\n", filePath, err)
	}

	// Create the AST for the source file
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, filePath, src, parser.ParseComments)
	if err != nil {
		log.Fatalf("Error parsing file %s: %v\n", filePath, err)
	}

	// Traverse the AST
	for _, f := range node.Decls {
		if fn, isFn := f.(*ast.FuncDecl); isFn && strings.HasPrefix(fn.Name.Name, "Test") {
			// Check if the function has a docstring
			if fn.Doc != nil {
				doc := fn.Doc.Text()
				relativePath := strings.TrimPrefix(filePath, "../../tests/integration/")
				link := fmt.Sprintf("[%s](%s#L%d)", relativePath, filePath, fset.Position(fn.Pos()).Line)

				// Split the docstring based on the separator "========"
				parts := strings.Split(doc, "\n========\n")
				var shortDescription, longDescription string
				if len(parts) > 1 {
					shortDescription = strings.TrimSpace(parts[0])
					longDescription = strings.TrimSpace(parts[1])
				} else {
					shortDescription = strings.TrimSpace(doc)
					longDescription = ""
				}

				// Format the description
				description := shortDescription
				if longDescription != "" {
					description += fmt.Sprintf("<details><summary>Details</summary>%s</details>", longDescription)
				}
				// for formatting the description in markdown table,
				// replace newlines with spaces
				description = strings.ReplaceAll(description, "\n", " ")

				fmt.Fprintf(out, "| %s | %s | %s |\n", link, fn.Name.Name, description)
			}
		}
	}
}
