package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
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

	errorStatusCode := false

	// Walk through the directory
	err = filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		// Only process .go files
		if !info.IsDir() && strings.HasSuffix(info.Name(), ".go") && !strings.HasSuffix(info.Name(), "_test.go") {
			functionsMissingDocStrings := extractDocstrings(path, out)
			if len(functionsMissingDocStrings) > 0 {
				fmt.Printf("The following test functions in %s are missing docstrings:\n", path)
				for _, fn := range functionsMissingDocStrings {
					fmt.Printf("\t%s\n", fn)
				}
				errorStatusCode = true
			}
		}
		return nil
	})
	if err != nil {
		log.Fatalf("Error walking the path %q: %v\n", dir, err)
	}

	fmt.Printf("Documentation generated successfully in %s\n", outputFile)

	if errorStatusCode {
		os.Exit(1)
	}
}

// extractDocstrings extracts the docstrings from the Go source file and writes them to the output file
// in a markdown table format.
// It returns a list of test functions that are missing docstrings.
func extractDocstrings(filePath string, out *os.File) []string {
	// Check if the file exists and is within the allowed directory
	allowedDir := "../../tests/integration/" // Adjust this to your specific allowed directory
	if !strings.HasPrefix(filePath, allowedDir) {
		log.Fatalf("Error: File path %s is outside the allowed directory\n", filePath)
	}

	// Read the Go source file
	src, err := os.ReadFile(filePath)
	if err != nil {
		log.Fatalf("Error reading file %s: %v\n", filePath, err)
	}

	// Create the AST for the source file
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, filePath, src, parser.ParseComments)
	if err != nil {
		log.Fatalf("Error parsing file %s: %v\n", filePath, err)
	}

	functionsMissingDocstrings := []string{}

	// Files that do not contain test functions are excluded from the documentation.
	fileNameWritten := false

	// Traverse the AST
	for _, f := range node.Decls {
		if fn, isFn := f.(*ast.FuncDecl); isFn && strings.HasPrefix(fn.Name.Name, "Test") {
			// Check if the function has a docstring
			if fn.Doc != nil {

				if !fileNameWritten {
					relativePath := strings.TrimPrefix(filePath, "../../tests/integration/")
					doclink := fmt.Sprintf("[%s](%s)", relativePath, filePath)
					fmt.Fprintf(out, "# %s \n", doclink)
					fmt.Fprintf(out, "<details><summary> Test Specifications </summary>\n\n")

					// Write table header
					fmt.Fprintf(out, "| Function | Short Description |\n")
					fmt.Fprintf(out, "|----------|-------------------|\n")
					fileNameWritten = true
				}

				doc := fn.Doc.Text()
				link := fmt.Sprintf("[%s](%s#L%d)", fn.Name.Name, filePath, fset.Position(fn.Pos()).Line)

				// Split the docstring based on the separator "========"
				parts := strings.Split(doc, "\n@Long Description@\n")
				var shortDescription, longDescription string
				if len(parts) > 1 {
					shortDescription = strings.TrimSpace(parts[0])
					longDescription = strings.TrimSpace(parts[1])
				} else {
					shortDescription = strings.TrimSpace(doc)
					longDescription = ""
				}

				// Format the description

				// avoid breaking the table format: newlines need to be replaced
				// for the short description, use spaces
				shortDescription = strings.ReplaceAll(shortDescription, "\n", " ")
				// for the long description, use breaks
				longDescription = strings.ReplaceAll(longDescription, "\n", "<br>")

				description := shortDescription
				if longDescription != "" {
					description += fmt.Sprintf("<details><summary>Details</summary>%s</details>", longDescription)
				}

				fmt.Fprintf(out, " %s | %s |\n", link, description)
			} else {
				functionsMissingDocstrings = append(functionsMissingDocstrings, fn.Name.Name)

			}
		}
	}
	if fileNameWritten {
		fmt.Fprintf(out, "</details>\n\n")
	}
	return functionsMissingDocstrings
}
