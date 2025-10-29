# Implementation of cost analysis by Hoare Logic

In the `src` folder you will find:

- `Common.hs`, `PrettyPrinter.hs` - Various utility functions
- `Gentzen.hs` - Implementation of Propositional calculus
- `TNT.hs` - Implementation of Typographical Number Theory
- `Hoare.hs` - Implementation of Hoare logic (on top of Propositional calculus + Number theory)
- `Imp.hs` - Implementation of a simple imperative programming language (the commands correspond to the rules of Hoare logic)
- `Costs.hs` - Definition of cost expressions and evaluation of arithmetic and boolean costs
- `CostExp.hs` - Extension of Hoare logic with cost-annotated proofs

## Running

- `ghci -isrc -iexamples` and `> :l Main.hs`

- Once in the REPL mode, evaluate `putStrLn $ pr proof`