'use strict';
const path = require('path');
const TsMacros = require("ts-macros").default;

module.exports = {
    devtool: 'inline-source-map',
	entry: './tests/parser_tests.ts',
	output: {
		filename: 'main.js',
		path: path.resolve(__dirname, 'dist')
	},
    module: {
        rules: [
            {
                test: /\.([cm]?ts|tsx)$/,
                loader: 'ts-loader',
                options: {
                    getCustomTransformers: (program) => ({
                        before: [TsMacros(program)]
                    }),
                }
            },
        ],
    },
    resolve: {
        extensions: [ '.ts', '.tsx', '.js' ],
        extensionAlias: {
            '.ts': ['.js', '.ts'],
            '.cts': ['.cjs', '.cts'],
            '.mts': ['.mjs', '.mts']
        }
    }
};