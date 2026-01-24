
## 🌐 Web Deployment

To deploy your game to the web (like the official Lean Game Server):

1.  **Host on GitHub**: Push this repository to GitHub.
2.  **Enable Actions**: Go to "Settings > Actions" and ensure workflows are enabled.
3.  **Use the Action**: Create a `.github/workflows/deploy.yml` using the [standard lean4game template](https://github.com/leanprover-community/lean4game/blob/main/.github/workflows/deploy.yml).
4.  **Play**: Your game will be available at `https://<username>.github.io/<repo>/`.

*Note: You cannot easily "run" the full web UI locally without cloning the separate frontend repository.*
