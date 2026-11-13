// The template's own view state: the session tree, its flattened rows, and the values the page's
// controls carry.

/** One node of the session tree `buildTree` builds from the entries' `parentId` links. */
type TreeNode = {
  entry: SessionEntry;
  /** Oldest first. */
  children: TreeNode[];
  /** The newest `label` entry's text for this entry. */
  label: string | undefined;
};

/** A vertical guide line drawn at one indent level of a tree row's prefix. */
type Gutter = { position: number; show: boolean };

/** One row of the flattened tree: its node and how its prefix draws. */
type FlatNode = {
  node: TreeNode;
  indent: number;
  showConnector: boolean;
  isLast: boolean;
  gutters: Gutter[];
  isVirtualRootChild: boolean;
  multipleRoots: boolean;
};

/** A depth-first walk step of `flattenTree`. */
type TreeWalkFrame = [
  node: TreeNode,
  indent: number,
  justBranched: boolean,
  showConnector: boolean,
  isLast: boolean,
  gutters: Gutter[],
  isVirtualRootChild: boolean,
];

/** A depth-first walk step of `recalculateVisualStructure`, over entry ids. */
type VisibleWalkFrame = [
  nodeId: string,
  indent: number,
  justBranched: boolean,
  showConnector: boolean,
  isLast: boolean,
  gutters: Gutter[],
  isVirtualRootChild: boolean,
];

/** The tree filter a `.filter-btn` selects (its `data-filter`). */
type FilterMode = "default" | "no-tools" | "user-only" | "labeled-only" | "all";

/** A sidebar filter button (template.html: each has a `data-filter`). */
type FilterButton = HTMLButtonElement & { readonly dataset: DOMStringMap & { readonly filter: FilterMode } };

/** A message's copy-link button (`renderCopyLinkButton` always writes `data-entry-id`). */
type CopyLinkButton = HTMLButtonElement & { readonly dataset: DOMStringMap & { readonly entryId: string } };

/** Where `navigateTo` scrolls the messages. */
type ScrollMode = "target" | "bottom" | "none";

/** A `<skill …>` block at the start of a user message (`parseSkillBlock`). */
type SkillBlock = { name: string; location: string; content: string; userMessage: string | undefined };

/** A content block as the text helpers read it: any block, of which only `text` ones carry text. */
type ContentBlockText = { readonly type: string; readonly text?: string };

/** The focused element `isEditableTarget` inspects: an HTML or other (SVG, MathML) element. */
type FocusedElement = {
  readonly tagName: string;
  /** HTML elements only. */
  readonly isContentEditable?: boolean;
  closest?(selectors: string): Element | null;
};
