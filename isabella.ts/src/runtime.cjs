/**
 * Runtime loader for js_of_ocaml output
 *
 * This CommonJS module loads the js_of_ocaml compiled JavaScript
 * and exports the Isabella object. In CommonJS context, js_of_ocaml
 * exports to module.exports rather than globalThis.
 */

// Load the js_of_ocaml output
const jsoo = require('./isabella.js');

// Set globalThis.Isabella for access by ES modules
globalThis.Isabella = jsoo.Isabella;

// Also export it directly
module.exports = jsoo.Isabella;
