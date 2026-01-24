
import Lean
import Game.Widgets.MultipleChoice
import ProofWidgets.Component.HtmlDisplay




open Lean Elab Tactic ProofWidgets
open scoped Json


syntax (name := complexQuizT) "ComplexQuiz" str "[" term,* "]" num : tactic


@[tactic complexQuizT]
def evalComplexQuizT : Tactic := fun stx => do
  let qStx := stx[1]
  let optsStx := stx[3]
  let idxStx := stx[5]
  
  -- Extract question string
  let some question := qStx.isStrLit?
    | throwErrorAt qStx "Expected string literal for question"
  
  -- Extract correct index
  let some correctIndex := idxStx.isNatLit?
    | throwErrorAt idxStx "Expected natural number for correct index"
    
  -- Extract options array
  let mut options := #[]
  for arg in optsStx.getSepArgs do
    if let some s := arg.isStrLit? then
      options := options.push s
    else if let some s := arg.isNatLit? then
      options := options.push (toString s)
    else
      -- Try to get the raw text if it's not a literal but we want to show it
      options := options.push (arg.reprint.getD "option")




  let h := hash MultipleChoice.javascript
  let props := json% { 
    question: $(question), 
    options: $(options), 
    correctIndex: $(correctIndex) 
  }
  Widget.savePanelWidgetInfo h (pure props) stx




