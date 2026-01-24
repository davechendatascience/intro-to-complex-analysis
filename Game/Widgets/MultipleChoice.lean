import ProofWidgets.Component.HtmlDisplay
import Lean.Server.Rpc.Basic

open Lean Server ProofWidgets

structure MultipleChoiceProps where
  question : String
  options : Array String
  correctIndex : Nat
  deriving RpcEncodable

@[widget_module]
def MultipleChoice : Component MultipleChoiceProps where
  javascript := "
    import * as React from 'react';
    export default function MultipleChoice(props) {
      const [selected, setSelected] = React.useState(null);
      const [submitted, setSubmitted] = React.useState(false);

      const handleClick = (idx) => {
        setSelected(idx);
        setSubmitted(true);
      };

      return React.createElement('div', { className: 'mc-container' },
        React.createElement('h3', null, props.question),
        props.options.map((opt, idx) => 
          React.createElement('button', {
            key: idx,
            onClick: () => handleClick(idx),
            style: {
              display: 'block',
              margin: '5px',
              padding: '8px',
              backgroundColor: submitted && idx === props.correctIndex ? 'lightgreen' : 
                               submitted && idx === selected && idx !== props.correctIndex ? 'lightcoral' : 
                               '#f0f0f0'
            }
          }, opt)
        ),
        submitted && (selected === props.correctIndex 
          ? React.createElement('p', { style: { color: 'green' } }, 'Correct!') 
          : React.createElement('p', { style: { color: 'red' } }, 'Try again!'))
      );
    }
  "
