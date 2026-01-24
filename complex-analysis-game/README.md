# Complex Analysis Game

An interactive introduction to Complex Analysis, based on the open-access textbook **"Complex Analysis" by Howell & Mathews**. 

Built with [Lean 4](https://leanprover.github.io/) and the [Lean 4 Game Project](https://github.com/leanprover-community/lean4game).

## 🚀 Milestones

- [x] **Project Initialization**: Setup Lean 4 environment, GameServer, and fix Windows build issues (path encoding).
- [x] **Level 1: The Basics**: Implemented fundamental complex number properties (Real/Imaginary parts, Conjugates).
- [ ] **Content Migration**: 
    - [ ] Arithmetic & Modulus
    - [ ] The Complex Plane (Geometry)
    - [ ] Analytic Functions
    - [ ] Integration
- [x] **Interactive Features**:
    - [x] **Multiple Choice Quizzes**: Custom `ComplexQuiz` tactic/widget for conceptual testing.
    - [x] **Loogle Integration**: AI-powered theorem search directly in the VS Code environment.
- [x] **Web Deployment**: Configured for the official [Lean Game Server](https://adam.math.hhu.de).


## 🛠️ Local Development

### Prerequisites
- VS Code
- Lean 4 (via `elan`)

### Setup
1. Open this folder in VS Code.
2. Run `lake build` to compile the dependencies.
3. Open any file in `Game/Levels/` to start playing!

## 📚 Credits
- **Content**: [Howell & Mathews](http://seeds.thekeep.org/complex_analysis/)
- **Engine**: [lean4game](https://github.com/leanprover-community/lean4game)
