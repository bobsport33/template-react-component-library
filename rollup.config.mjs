import resolve from "@rollup/plugin-node-resolve";
import commonjs from "@rollup/plugin-commonjs";
import babel from "@rollup/plugin-babel";
import postcss from "rollup-plugin-postcss";

import packageJson from "./package.json" assert { type: "json" };

export default [
    {
        input: "src/index.js",
        output: [
            {
                file: packageJson.module,
                format: "esm",
                sourcemap: true,
            },
        ],
        plugins: [
            resolve({ extensions: [".js", ".jsx"] }),
            commonjs(),
            babel({
                extensions: [".js", ".jsx"],
                babelHelpers: "runtime", // Use babel runtime helpers
                presets: ["@babel/preset-env", "@babel/preset-react"], // Presets for babel
                plugins: ["@babel/plugin-transform-runtime"], // Plugin for babel runtime
            }),
            postcss(), // Add your postcss plugin if needed
        ],
        external: [
            ...Object.keys(packageJson.peerDependencies || {}),
            "node_modules/**",
        ],
    },
];
