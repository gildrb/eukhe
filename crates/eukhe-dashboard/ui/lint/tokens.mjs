// The lint rule `eukhe/token-literals`: a presentation value written outside
// the token source (src/tokens.stylex.ts) is an error. vite.config.ts turns
// it on for src/; src/tokens.test.ts applies the same patterns to
// global.css, which the linter does not read.
//
// It reports, in every string and template part:
//   - a color: `#rgb`..`#rrggbbaa`, a color function (`rgb(`, `light-dark(`, ...),
//     or a named color as the whole value of a color property;
//   - a length other than zero (`px`, `em`, `rem`, viewport units except 100);
//   - a duration other than zero (`150ms`, `2s`);
//   - an easing function (`cubic-bezier(`, `linear(`, `steps(`);
// and every number or non-keyword string given to a property whose value is
// a token by nature (z-index, font weight and size, line height, opacity,
// letter spacing, durations and easings), or to a Radix offset or lucide
// stroke width in JSX. 0 is a value nowhere; opacity 1 is full opacity.

import { definePlugin, defineRule } from "vite-plus/lint/plugins";

const TOKEN_SOURCE = /[\\/]tokens\.stylex\.ts$/;

const PATTERNS = [
  { what: "a color", test: /#[0-9a-f]{3,8}(?![\w-])/i },
  {
    what: "a color",
    test: /(?<![\w-])(?:rgba?|hsla?|hwb|lab|lch|oklab|oklch|color|color-mix|light-dark)\(/i,
  },
  { what: "an easing", test: /(?<![\w-])(?:cubic-bezier|linear|steps)\(/i },
];

const LENGTH =
  /(?<![\w.#-])-?(\d*\.?\d+)(px|rem|em|ch|ex|pt|pc|cm|mm|in|vw|vh|dvh|svh|lvh|vmin|vmax)(?![\w-])/gi;
const VIEWPORT = { vw: true, vh: true, dvh: true, svh: true, lvh: true, vmin: true, vmax: true };
const DURATION = /(?<![\w.#-])(\d*\.?\d+)(ms|s)(?![\w-])/gi;

/** Properties whose every value is a token: a number or a free string there is a literal. */
const TOKEN_PROPERTIES = {
  zIndex: true,
  fontWeight: true,
  fontSize: true,
  lineHeight: true,
  letterSpacing: true,
  opacity: true,
  animationDuration: true,
  animationDelay: true,
  transitionDuration: true,
  transitionDelay: true,
  animationTimingFunction: true,
  transitionTimingFunction: true,
  duration: true,
  delay: true,
  ease: true,
  easing: true,
};
const KEYWORDS = {
  inherit: true,
  initial: true,
  unset: true,
  revert: true,
  normal: true,
  none: true,
  auto: true,
  linear: true,
  ease: true,
  "ease-in": true,
  "ease-out": true,
  "ease-in-out": true,
  "step-start": true,
  "step-end": true,
};

/** JSX props that take pixels or milliseconds as numbers. */
const NUMERIC_PROPS = {
  sideOffset: true,
  alignOffset: true,
  collisionPadding: true,
  arrowPadding: true,
  strokeWidth: true,
  delayDuration: true,
  skipDelayDuration: true,
};

const COLOR_PROPERTY =
  /color|background|fill|stroke|outline|border|shadow|caret|accent|decoration/i;
const NAMED_COLORS = new Set(
  (
    "aliceblue antiquewhite aqua aquamarine azure beige bisque black blanchedalmond blue " +
    "blueviolet brown burlywood cadetblue chartreuse chocolate coral cornflowerblue cornsilk " +
    "crimson cyan darkblue darkcyan darkgoldenrod darkgray darkgreen darkgrey darkkhaki " +
    "darkmagenta darkolivegreen darkorange darkorchid darkred darksalmon darkseagreen " +
    "darkslateblue darkslategray darkslategrey darkturquoise darkviolet deeppink deepskyblue " +
    "dimgray dimgrey dodgerblue firebrick floralwhite forestgreen fuchsia gainsboro ghostwhite " +
    "gold goldenrod gray green greenyellow grey honeydew hotpink indianred indigo ivory khaki " +
    "lavender lavenderblush lawngreen lemonchiffon lightblue lightcoral lightcyan " +
    "lightgoldenrodyellow lightgray lightgreen lightgrey lightpink lightsalmon lightseagreen " +
    "lightskyblue lightslategray lightslategrey lightsteelblue lightyellow lime limegreen linen " +
    "magenta maroon mediumaquamarine mediumblue mediumorchid mediumpurple mediumseagreen " +
    "mediumslateblue mediumspringgreen mediumturquoise mediumvioletred midnightblue mintcream " +
    "mistyrose moccasin navajowhite navy oldlace olive olivedrab orange orangered orchid " +
    "palegoldenrod palegreen paleturquoise palevioletred papayawhip peachpuff peru pink plum " +
    "powderblue purple rebeccapurple red rosybrown royalblue saddlebrown salmon sandybrown " +
    "seagreen seashell sienna silver skyblue slateblue slategray slategrey snow springgreen " +
    "steelblue tan teal thistle tomato turquoise violet wheat white whitesmoke yellow yellowgreen"
  ).split(" "),
);

/** The first presentation value in `text`, described, or null. */
export function literalIn(text) {
  for (const { what, test } of PATTERNS) {
    const found = test.exec(text);
    if (found) return `${what} (${found[0]})`;
  }
  for (const found of text.matchAll(LENGTH)) {
    const value = Number(found[1]);
    const unit = (found[2] ?? "").toLowerCase();
    const viewport = Object.hasOwn(VIEWPORT, unit) && value === 100;
    if (value !== 0 && !viewport) return `a length (${found[0]})`;
  }
  for (const found of text.matchAll(DURATION)) {
    if (Number(found[1]) !== 0) return `a duration (${found[0]})`;
  }
  return null;
}

/** The CSS property a value sits under: the nearest key that is not a condition (`default`, `:hover`, `@media`, `[media.touch]`). */
function propertyOf(node) {
  for (let at = node; at?.parent; at = at.parent) {
    const parent = at.parent;
    if (parent.type === "Property" && parent.value === at) {
      if (parent.computed) continue;
      const key = parent.key.type === "Identifier" ? parent.key.name : parent.key.value;
      if (typeof key !== "string") return null;
      if (key === "default" || key.startsWith(":") || key.startsWith("@")) continue;
      return key;
    }
    const nested = ["ObjectExpression", "ArrayExpression", "UnaryExpression"].includes(parent.type);
    if (!nested) return null;
  }
  return null;
}

const tokenLiterals = defineRule({
  meta: {
    type: "problem",
    docs: { description: "Presentation values come from src/tokens.stylex.ts." },
    messages: {
      literal:
        "{{what}} is written outside the token source: name it in src/tokens.stylex.ts and use the token.",
    },
  },
  create(context) {
    if (TOKEN_SOURCE.test(context.filename)) return {};
    const report = (node, what) => context.report({ node, messageId: "literal", data: { what } });
    const checkText = (node, text) => {
      const what = literalIn(text);
      if (what) report(node, what);
    };
    return {
      Literal(node) {
        if (node.regex) return;
        const property = propertyOf(node);
        if (typeof node.value === "string") {
          checkText(node, node.value);
          const token = property && Object.hasOwn(TOKEN_PROPERTIES, property);
          if (token && !Object.hasOwn(KEYWORDS, node.value)) {
            report(node, `the ${property} value "${node.value}"`);
          } else if (
            property &&
            COLOR_PROPERTY.test(property) &&
            NAMED_COLORS.has(node.value.toLowerCase())
          ) {
            report(node, `a color (${node.value})`);
          }
          return;
        }
        if (
          typeof node.value === "number" &&
          property &&
          Object.hasOwn(TOKEN_PROPERTIES, property)
        ) {
          const identity = node.value === 0 || (property === "opacity" && node.value === 1);
          if (!identity) report(node, `the ${property} value ${node.raw}`);
        }
      },
      TemplateElement(node) {
        checkText(node, node.value.cooked ?? node.value.raw);
      },
      JSXAttribute(node) {
        const name = node.name.type === "JSXIdentifier" ? node.name.name : "";
        if (!Object.hasOwn(NUMERIC_PROPS, name)) return;
        const value = node.value;
        if (value?.type !== "JSXExpressionContainer") return;
        const inner =
          value.expression.type === "UnaryExpression"
            ? value.expression.argument
            : value.expression;
        if (inner.type === "Literal" && typeof inner.value === "number" && inner.value !== 0) {
          report(node, `the ${name} value ${inner.raw}`);
        }
      },
    };
  },
});

export default definePlugin({
  meta: { name: "eukhe" },
  rules: { "token-literals": tokenLiterals },
});
