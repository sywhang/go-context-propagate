// Copyright (c) 2021 Uber Technologies, Inc.
//
// Licensed under the Uber Non-Commercial License (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at the root directory of this project.
//
// See the License for the specific language governing permissions and
// limitations under the License.

package propagate

// The tool implemented in the propagate package parses and loads Go source files as ASTs
//  and uses these to construct a call graph.
//
// At a high level, the context propagation algorithm takes the following input:
//    - a list of "leaf functions" (package path/name and function name) - these represent library API
//      calls that currently do not take context as an argument but are meant to take it (as the first
//      argument) after the refactoring
//    - the name and type of context parameter (as strings)
//    - the names of functions where the context propagation is supposed to stop (optional)
//
// Given this input, the algorithm visits all nodes in the call graph to locate calls to leaf functions.
// Once these are available, the algorithm follows the call chains originating from these functions,
// collecting both function definitions that need an additional context argument, and call sites
// for theses additional functions that also have to be modified. The algorithm stops visiting call graph
// nodes either when it visits them all or when it encounters a function that is explicitly marked as one
// where the propagation should stop. When processing function calls, the algorithm also keeps track of
// additional language constructs that need to modified in concert with function definition changes
// (e.g. named function types).
//
// Once the list of function definitions, the list of call sites, and the list of additional language
// constructs to be modified are collected, the algorithm visits ASTs one by one and modifies all
// required parts of the program.

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"go/types"
	"html/template"
	"io/ioutil"
	"log"
	"os"
	"sort"
	"strings"

	cg "golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/callgraph/rta"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

// Run is the main entry point for the whole context propgatation process.
func Run(configFilePath string, debugFilePath string, srcPaths []string, debugLevel int) {

	results := propagate(configFilePath, debugFilePath, srcPaths, debugLevel)

	// write modified files to the same locations as original files with the added "mod" extension
	for p, nodes := range results {
		for n, ind := range nodes {
			var buf bytes.Buffer
			err := format.Node(&buf, p.Fset, n)
			if err != nil {
				ast.Print(p.Fset, n)
				log.Fatal(err)
			}
			err = ioutil.WriteFile(p.CompiledGoFiles[ind]+".mod", buf.Bytes(), 0644)
			if err != nil {
				log.Fatal(err)
			}
		}
	}

}

// propagate is the main driver for the whole context propgatation process.
func propagate(configFilePath string, debugFilePath string, srcPaths []string, debugLevel int) map[*packages.Package]map[*ast.File]int {

	cfg := initialize(configFilePath, debugLevel)

	loadPaths := cfg.LoadPaths
	if srcPaths != nil && len(srcPaths) > 0 {
		// if paths passed explicitly - use them
		loadPaths = srcPaths
	}

	loadConfig := &packages.Config{Mode: packages.LoadAllSyntax, Tests: true}
	argsSize := 0
	for _, s := range loadPaths {
		argsSize += len(s)
	}
	iter := (argsSize / argBytesLimit) + 1
	inc := len(loadPaths) / iter

	var initialLoaded []*packages.Package
	numPaths := len(loadPaths)
	if numPaths > inc {
		cfg.largeCode = true
		if cfg.debugLevel > 0 {
			fmt.Println("INCREMENTAL LOADING")
		}
		cfg.fsets = make(map[*types.Package]*token.FileSet)
	} else if cfg.debugLevel > 0 {
		fmt.Println("ONE-TIME LOADING")
	}
	for i := 0; i < numPaths; i += inc {
		end := numPaths
		if i+inc < numPaths {
			end = i + inc
		}

		allLoadPaths := append(loadPaths[i:end], cfg.LibPkgPath)
		if cfg.LibIface == "" {
			allLoadPaths = loadPaths[i:end]
		}

		loaded, err := packages.Load(loadConfig, allLoadPaths...)
		if err != nil {
			log.Fatal(err)
		}

		if cfg.largeCode && len(loaded) > 0 {
			for _, l := range loaded {
				cfg.fsets[l.Types] = l.Fset
			}
		}

		initialLoaded = append(initialLoaded, loaded...)

	}

	// ignore packages that have not been loaded correctly, but warn the user about it
	for _, p := range initialLoaded {
		if len(p.Errors) > 0 {
			// ignore this package

			// if the debug level is high enough, print detailed info
			if cfg.debugLevel > 1 {
				fmt.Println("PACKAGE " + p.Name + " (AT " + p.PkgPath + ") BUILD ERRORS: ")
				for _, e := range p.Errors {
					fmt.Println(e)
				}
			}

			// if debug is enabled at all, collect names of packages that filed to load
			if cfg.debugLevel > 0 {
				cfg.debugData.Excluded = append(cfg.debugData.Excluded, "package "+p.Name+" at "+p.PkgPath)
			}
			continue
		}
		cfg.initial = append(cfg.initial, p)

	}

	prog, pkgs := ssautil.AllPackages(cfg.initial, ssa.GlobalDebug)

	var cgRoots []*ssa.Function
	// we could use prog.Build() instead but this would create a call graph including all dependencies
	for _, p := range pkgs {
		if p != nil {
			p.Build()
		}
	}

	var graph *cg.Graph
	if cfgType == cfgRTA {
		if cfg.debugLevel > 0 {
			fmt.Println("GOPATH:", os.Getenv("GOPATH"))
		}
		// use RTA to construct the callgraph; CHA-style construction overapproximates calls made
		// via functions passed as parameters to a larger extent than RTA (creates edges for all
		// functions whose signature matches the function parameter rather than for some in case of RTA)

		for f, _ := range ssautil.AllFunctions(prog) {
			cgRoots = append(cgRoots, f)
		}
		res := rta.Analyze(cgRoots, true)
		if res == nil {
			log.Fatalf("error building RTA callgraph")
		}
		graph = res.CallGraph
	} else if cfgType == cfgCHA {
		// callgraph constructed using CHA algorithm
		graph = cha.CallGraph(prog)
	} else {
		// callgraph constructed using points-to analysis
		// TODO: can't make it to include all required files...
		var ptrConfig pointer.Config
		mainPkgs := ssautil.MainPackages(pkgs)

		// add synthetic main packages to include tests
		mainPkgsMap := make(map[*ssa.Package]bool)
		for _, p := range mainPkgs {
			mainPkgsMap[p] = true
		}
		for _, p := range pkgs {
			if !mainPkgsMap[p] {
				CreateTestMainPackage(prog, p)
			}
		}

		mainPkgs = ssautil.MainPackages(prog.AllPackages())
		ptrConfig.Mains = mainPkgs
		ptrConfig.BuildCallGraph = true
		ptrConfig.Reflection = true
		res, err := pointer.Analyze(&ptrConfig)
		if err != nil {
			log.Fatalf("error creating call graph using points-to analysis")
		}
		graph = res.CallGraph

	}
	graph.DeleteSyntheticNodes()

	transformer := transformerConfig{
		config:           cfg,
		astIfaceModified: make(map[*ast.InterfaceType]bool),
	}

	analyzer := analyzerConfig{
		config:           cfg,
		prog:             prog,
		graph:            graph,
		mapAndSliceFuncs: make(map[*ssa.Package]map[*types.Signature]bool),
	}

	(&analyzer).analyze()
	res := (&transformer).transform()

	outputDebugInfo(debugFilePath, cfg)
	return res
}

// initialize performs tool initialization.
func initialize(configFilePath string, debugLevel int) *config {
	if configFilePath == "" {
		fmt.Fprintln(os.Stderr, "USAGE:")
		flag.PrintDefaults()
		os.Exit(1)
	}

	buf, ok := ioutil.ReadFile(configFilePath)
	if ok != nil {
		log.Fatalf("error reading config file " + configFilePath)
	}

	jsonCfg := jsonConfig{
		ExtEmbedTypes:    make(typeInfo),
		LibFns:           make(fnReplacementInfo),
		PropagationStops: make(fnInfo),
	}

	err := json.Unmarshal(buf, &jsonCfg)
	if err != nil {
		log.Fatalf("error unmarshalling file " + configFilePath + ":\n" + err.Error())
	}

	cfg := config{
		jsonConfig:          &jsonCfg,
		debugLevel:          debugLevel,
		largeCode:           false,
		fnVisited:           make(map[uniquePosInfo]int),
		callSites:           make(map[uniquePosInfo]*replacementInfo),
		callSitesRenamed:    make(map[uniquePosInfo]string),
		ifaceModified:       make(map[*types.Interface]map[string]bool),
		fnParamsVisited:     make(map[uniquePosInfo]bool),
		renameParamsVisited: make(map[uniquePosInfo]bool),
	}

	if cfg.CtxParamInvalid == "" {
		log.Fatalf("artificial context expression (CtxParamInvalid) must be specified in the config file")
	}

	if !(len(cfg.CtxCustomPkgPath) == 0 && len(cfg.CtxCustomPkgName) == 0 && len(cfg.CtxCustomParamType) == 0 && len(cfg.CtxCustomExprExtract) == 0) &&
		!(len(cfg.CtxCustomPkgPath) > 0 && len(cfg.CtxCustomPkgName) > 0 && len(cfg.CtxCustomParamType) > 0 && len(cfg.CtxCustomExprExtract) > 0) {
		log.Fatalf("either all or none of the custom context options should be specified in the config file")
	}

	// context param type qualified with both path and name
	cfg.ctxParamTypeWithPkgPathName = getQualifiedType(cfg.CtxParamType, cfg.CtxPkgPath, cfg.CtxPkgName)
	if len(cfg.CtxCustomParamType) > 0 {
		cfg.ctxCustomParamTypeWithPkgPathName = getQualifiedType(cfg.CtxCustomParamType, cfg.CtxCustomPkgPath, cfg.CtxCustomPkgName)
	}

	cfg.commonCallReplacement = replacementInfo{"", 1, nil, "", cfg.CtxParamName}

	return &cfg
}

// outputDebugInfo outputs debug info either to standard output or to
// a file for further processing.
func outputDebugInfo(debugFilePath string, cfg *config) {
	if cfg.debugLevel <= 0 {
		return
	}
	if debugFilePath != "" {
		debugFile, err := os.OpenFile(debugFilePath, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0755)
		if err != nil {
			log.Fatalf("error creating debug file " + debugFilePath)
		}
		// add generated debug data to a file
		debugData, err := json.Marshal(cfg.debugData)
		if err != nil {
			log.Fatalf("error writing debug file " + debugFilePath)
		}
		debugFile.WriteString(string(debugData))
		debugFile.Close()
	} else {
		// print generated debug data unless already printed at higher debug level
		if cfg.debugLevel < 2 && len(cfg.debugData.Excluded) > 0 {
			fmt.Println("PACKAGES EXCLUDED DUE TO BUILD ERRORS:")
			for _, pe := range cfg.debugData.Excluded {
				fmt.Println(pe)
			}
		}
		if cfg.debugLevel > 0 && len(cfg.debugData.Warnings) > 0 {
			fmt.Println("CODE TRANSFORMATION WARNINGS:")
			for _, c := range cfg.debugData.Warnings {
				fmt.Println(c["msg"])
				fmt.Println(c["file"] + " (line " + c["line"] + ")")
			}
		}
	}
}

// CreateTestMainPackage creates and returns a synthetic "testmain"
// package for the specified package if it defines tests, benchmarks or
// executable examples, or nil otherwise.  The new package is named
// "main" and provides a function named "main" that runs the tests,
// similar to the one that would be created by the 'go test' tool.
//
// Subsequent calls to prog.AllPackages include the new package.
// The package pkg must belong to the program prog.
//
// Deprecated: Use golang.org/x/tools/go/packages to access synthetic
// testmain packages.
func CreateTestMainPackage(prog *ssa.Program, pkg *ssa.Package) (*ssa.Package, error) {
	// Template data
	var data struct {
		Pkg                         *ssa.Package
		Tests, Benchmarks, Examples []*ssa.Function
		Main                        *ssa.Function
		Go18                        bool
	}
	data.Pkg = pkg

	// Enumerate tests.
	data.Tests, data.Benchmarks, data.Examples, data.Main = FindTests(pkg)
	if data.Main == nil &&
		data.Tests == nil && data.Benchmarks == nil && data.Examples == nil {
		return nil, nil
	}
	sort.Slice(data.Tests, func(i, j int) bool {
		return data.Tests[i].Pos() < data.Tests[j].Pos()
	})
	sort.Slice(data.Benchmarks, func(i, j int) bool {
		return data.Benchmarks[i].Pos() < data.Benchmarks[j].Pos()
	})
	sort.Slice(data.Examples, func(i, j int) bool {
		return data.Examples[i].Pos() < data.Examples[j].Pos()
	})

	// Synthesize source for testmain package.
	path := pkg.Pkg.Path() + "$testmain"
	tmpl := testmainTmpl
	if testingPkg := prog.ImportedPackage("testing"); testingPkg != nil {
		// In Go 1.8, testing.MainStart's first argument is an interface, not a func.
		data.Go18 = types.IsInterface(testingPkg.Func("MainStart").Signature.Params().At(0).Type())
	} else {
		// The program does not import "testing", but FindTests
		// returned non-nil, which must mean there were Examples
		// but no Test, Benchmark, or TestMain functions.

		// We'll simply call them from testmain.main; this will
		// ensure they don't panic, but will not check any
		// "Output:" comments.
		// (We should not execute an Example that has no
		// "Output:" comment, but it's impossible to tell here.)
		tmpl = examplesOnlyTmpl
	}
	var buf bytes.Buffer
	if err := tmpl.Execute(&buf, data); err != nil {
		log.Fatalf("internal error expanding template for %s: %v", path, err)
	}
	if false { // debugging
		fmt.Fprintln(os.Stderr, buf.String())
	}

	// Parse and type-check the testmain package.
	f, err := parser.ParseFile(prog.Fset, path+".go", &buf, parser.Mode(0))
	if err != nil {
		return nil, err
	}
	conf := types.Config{
		DisableUnusedImportCheck: true,
		Importer:                 testImporter{pkg},
	}
	files := []*ast.File{f}
	info := &types.Info{
		Types:      make(map[ast.Expr]types.TypeAndValue),
		Defs:       make(map[*ast.Ident]types.Object),
		Uses:       make(map[*ast.Ident]types.Object),
		Implicits:  make(map[ast.Node]types.Object),
		Scopes:     make(map[ast.Node]*types.Scope),
		Selections: make(map[*ast.SelectorExpr]*types.Selection),
	}
	testmainPkg, err := conf.Check(path, prog.Fset, files, info)
	if err != nil {
		return nil, err
	}

	// Create and build SSA code.
	testmain := prog.CreatePackage(testmainPkg, files, info, false)
	testmain.SetDebugMode(false)
	testmain.Build()
	testmain.Func("main").Synthetic = "test main function"
	testmain.Func("init").Synthetic = "package initializer"
	return testmain, nil
}

// An implementation of types.Importer for an already loaded SSA program.
type testImporter struct {
	pkg *ssa.Package // package under test; may be non-importable
}

func (imp testImporter) Import(path string) (*types.Package, error) {
	if p := imp.pkg.Prog.ImportedPackage(path); p != nil {
		return p.Pkg, nil
	}
	if path == imp.pkg.Pkg.Path() {
		return imp.pkg.Pkg, nil
	}
	return nil, fmt.Errorf("Not found pkg %v", path)
}

var testmainTmpl = template.Must(template.New("testmain").Parse(`
package main
import "io"
import "os"
import "testing"
import p {{printf "%q" .Pkg.Pkg.Path}}
{{if .Go18}}
type deps struct{}
func (deps) ImportPath() string { return "" }
func (deps) MatchString(pat, str string) (bool, error) { return true, nil }
func (deps) SetPanicOnExit0(bool) {}
func (deps) StartCPUProfile(io.Writer) error { return nil }
func (deps) StartTestLog(io.Writer) {}
func (deps) StopCPUProfile() {}
func (deps) StopTestLog() error { return nil }
func (deps) WriteHeapProfile(io.Writer) error { return nil }
func (deps) WriteProfileTo(string, io.Writer, int) error { return nil }
var match deps
{{else}}
func match(_, _ string) (bool, error) { return true, nil }
{{end}}
func main() {
	tests := []testing.InternalTest{
{{range .Tests}}
		{ {{printf "%q" .Name}}, p.{{.Name}} },
{{end}}
	}
	benchmarks := []testing.InternalBenchmark{
{{range .Benchmarks}}
		{ {{printf "%q" .Name}}, p.{{.Name}} },
{{end}}
	}
	examples := []testing.InternalExample{
{{range .Examples}}
		{Name: {{printf "%q" .Name}}, F: p.{{.Name}}},
{{end}}
	}
	m := testing.MainStart(match, tests, benchmarks, examples)
{{with .Main}}
	p.{{.Name}}(m)
{{else}}
	os.Exit(m.Run())
{{end}}
}
`))

var examplesOnlyTmpl = template.Must(template.New("examples").Parse(`
package main
import p {{printf "%q" .Pkg.Pkg.Path}}
func main() {
{{range .Examples}}
	p.{{.Name}}()
{{end}}
}
`))

// FindTests returns the Test, Benchmark, and Example functions
// (as defined by "go test") defined in the specified package,
// and its TestMain function, if any.
//
// Deprecated: Use golang.org/x/tools/go/packages to access synthetic
// testmain packages.
func FindTests(pkg *ssa.Package) (tests, benchmarks, examples []*ssa.Function, main *ssa.Function) {
	prog := pkg.Prog

	// The first two of these may be nil: if the program doesn't import "testing",
	// it can't contain any tests, but it may yet contain Examples.
	var testSig *types.Signature                              // func(*testing.T)
	var benchmarkSig *types.Signature                         // func(*testing.B)
	var exampleSig = types.NewSignature(nil, nil, nil, false) // func()

	// Obtain the types from the parameters of testing.MainStart.
	if testingPkg := prog.ImportedPackage("testing"); testingPkg != nil {
		mainStart := testingPkg.Func("MainStart")
		params := mainStart.Signature.Params()
		testSig = funcField(params.At(1).Type())
		benchmarkSig = funcField(params.At(2).Type())

		// Does the package define this function?
		//   func TestMain(*testing.M)
		if f := pkg.Func("TestMain"); f != nil {
			sig := f.Type().(*types.Signature)
			starM := mainStart.Signature.Results().At(0).Type() // *testing.M
			if sig.Results().Len() == 0 &&
				sig.Params().Len() == 1 &&
				types.Identical(sig.Params().At(0).Type(), starM) {
				main = f
			}
		}
	}

	// TODO(adonovan): use a stable order, e.g. lexical.
	for _, mem := range pkg.Members {
		if f, ok := mem.(*ssa.Function); ok &&
			ast.IsExported(f.Name()) &&
			strings.HasSuffix(prog.Fset.Position(f.Pos()).Filename, "_test.go") {

			switch {
			case testSig != nil && isTestSig(f, "Test", testSig):
				tests = append(tests, f)
			case benchmarkSig != nil && isTestSig(f, "Benchmark", benchmarkSig):
				benchmarks = append(benchmarks, f)
			case isTestSig(f, "Example", exampleSig):
				examples = append(examples, f)
			default:
				continue
			}
		}
	}
	return
}

// Given the type of one of the three slice parameters of testing.Main,
// returns the function type.
func funcField(slice types.Type) *types.Signature {
	return slice.(*types.Slice).Elem().Underlying().(*types.Struct).Field(1).Type().(*types.Signature)
}

// Like isTest, but checks the signature too.
func isTestSig(f *ssa.Function, prefix string, sig *types.Signature) bool {
	return isTest(f.Name(), prefix) && types.Identical(f.Signature, sig)
}

// isTest tells whether name looks like a test (or benchmark, according to prefix).
// It is a Test (say) if there is a character after Test that is not a lower-case letter.
// We don't want TesticularCancer.
// Plundered from $GOROOT/src/cmd/go/test.go
func isTest(name, prefix string) bool {
	if !strings.HasPrefix(name, prefix) {
		return false
	}
	if len(name) == len(prefix) { // "Test" is ok
		return true
	}
	return ast.IsExported(name[len(prefix):])
}
