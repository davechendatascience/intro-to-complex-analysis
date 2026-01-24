
import Game.Widgets.MultipleChoice
import Lean

open Lean Elab Command

syntax (name := quiz) "Quiz" str term term : command

@[command_elab quiz]
def elabQuiz : CommandElab := fun stx => do
  let question := stx[1].getString
  let optionsStx := stx[2]
  let correctIndexStx := stx[3]
  
  -- Verify the terms are valid (optional, but good)
  -- We just want to output the #html command
  
  -- Construct the term: <MultipleChoice ... />
  let html := <MultipleChoice 
    question={question} 
    options={optionsStx} -- This needs to be parsed as a term
    correctIndex={correctIndexStx} 
  >
  
  -- Ideally we would emit an info tree or something the game server understands.
  -- But for now, we just want to run the #html command *as part of elaboration*?
  -- No, #html is a command itself.
  
  -- We can macro expand "Quiz Q O I" -> "#html <MultipleChoice ... />"
