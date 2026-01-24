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
- [ ] **Web Deployment**: Deploy to GitHub Pages for easy student access (The game runs entirely in the browser!).
- [ ] **Interactive Features**:
    - [ ] **Multiple Choice Quizzes**: Develop custom `ProofWidgets` to allow students to answer conceptual questions before proving theorems.
    - [ ] **Visualizations**: interactive graphs of the complex plane.

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
