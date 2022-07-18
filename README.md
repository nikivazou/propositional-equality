# Code for Haskell'22 submission #40: How to Safely Use Extensionality in Liquid Haskell

- `propositional-equality` contains the code from sections 2, 3, and 4.
   To use Liquid Haskell to check all the code, run `stack test`. 
   

```
      -- section 2: unsound client
      test/Inconsistency.hs  

      -- section 3: library definitions and classy induction  
      Relation.Equality.Prop.hs

      -- section 4: examples are in test/
      4.1  Reverse.hs 
      4.2  RefinedDomains.hs 
      4.3  Map.hs
      4.4  Folds.hs
      4.5  RunTimeCheck.hs
      4.6  Readers.hs
      also Endofunctors.hs
```