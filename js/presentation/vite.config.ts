import { componentExplorer } from "@vscode/component-explorer-vite-plugin";
import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import { join } from "path";

export default defineConfig({
	plugins: [
		react(),
		componentExplorer({
			include: join(__dirname, "src/**/*.fixture.{ts,tsx}"),
			build: "all",
		}),
	],
});
