// The app's controls, each a Radix primitive where one exists: buttons
// with tooltips, segmented choices (ToggleGroup), list choices (a
// DropdownMenu radio group, the look of every other menu), checkboxes and
// text fields. Hit areas are 44px on touch screens.

import * as Checkbox from "@radix-ui/react-checkbox";
import * as Menu from "@radix-ui/react-dropdown-menu";
import * as ToggleGroup from "@radix-ui/react-toggle-group";
import * as Tooltip from "@radix-ui/react-tooltip";
import * as stylex from "@stylexjs/stylex";
import { Check, ChevronDown } from "lucide-preact";
import type { ButtonHTMLAttributes, ComponentChildren, JSX } from "preact";
import { forwardRef } from "react";
import { useMedia } from "../lib/media.ts";
import {
  colors,
  layer,
  media,
  opacity,
  radius,
  size,
  space,
  stroke,
  type,
  weight,
} from "../tokens.stylex.ts";
import { ui } from "../ui.ts";

type ButtonProps = Omit<ButtonHTMLAttributes, "label" | "size"> & {
  label: string;
  /** A keyboard shortcut shown in the tooltip. */
  keys?: string;
  children: ComponentChildren;
  side?: "top" | "bottom" | "left" | "right";
  /** Extra StyleX styles, merged after the button's own. */
  xstyle?: stylex.StyleXArray<stylex.CompiledStyles | boolean | null | undefined>;
};

/** A square icon button, named by `label` (its tooltip, where a pointer can hover). */
export const IconButton = forwardRef<HTMLButtonElement, ButtonProps>(function IconButton(
  { label, keys, children, side = "bottom", xstyle, ...rest },
  ref,
) {
  const hover = useMedia(media.hover);
  const button = (
    <button
      type="button"
      aria-label={label}
      {...rest}
      ref={ref}
      {...stylex.props(ui.reset, ui.focusRing, styles.iconButton, xstyle)}
    >
      {children}
    </button>
  );
  if (!hover) return button;
  return (
    <Tooltip.Root>
      <Tooltip.Trigger asChild>{button}</Tooltip.Trigger>
      <Tooltip.Portal>
        <Tooltip.Content
          side={side}
          sideOffset={parseFloat(space.x15)}
          {...stylex.props(styles.tooltip)}
        >
          {label}
          {keys ? <span {...stylex.props(styles.tooltipKeys)}>{keys}</span> : null}
        </Tooltip.Content>
      </Tooltip.Portal>
    </Tooltip.Root>
  );
});

/** A quiet text action (Copy, Retry, Edit): 14/20, its hit area 44px tall on touch. */
export function TextButton({
  children,
  strong = false,
  ...rest
}: ButtonHTMLAttributes & { strong?: boolean }) {
  return (
    <button
      type="button"
      {...rest}
      {...stylex.props(ui.reset, ui.focusRing, styles.textButton, strong && styles.textStrong)}
    >
      {children}
    </button>
  );
}

/** A labelled button: `primary` is filled with the text color. */
export function Button({
  children,
  kind = "secondary",
  ...rest
}: Omit<ButtonHTMLAttributes, "kind"> & {
  kind?: "primary" | "secondary" | "danger";
}) {
  return (
    <button
      type="button"
      {...rest}
      {...stylex.props(
        ui.reset,
        ui.focusRing,
        styles.button,
        kind === "primary" && styles.primary,
        kind === "danger" && styles.danger,
      )}
    >
      {children}
    </button>
  );
}

export type Option = { value: string; label: string };

/** Two to five exclusive choices in one rectangular track (Radix ToggleGroup). */
export function Segmented({
  label,
  options,
  value,
  onChange,
  compact = false,
}: {
  label: string;
  options: Option[];
  value: string | undefined;
  onChange: (value: string) => void;
  compact?: boolean;
}) {
  return (
    <ToggleGroup.Root
      type="single"
      aria-label={label}
      value={value ?? ""}
      onValueChange={(next) => {
        // A pressed choice stays chosen: Radix would clear it on a second press.
        if (next) onChange(next);
      }}
      {...stylex.props(styles.track, compact && styles.trackCompact)}
    >
      {options.map((option) => (
        <ToggleGroup.Item
          key={option.value}
          value={option.value}
          {...stylex.props(
            ui.reset,
            ui.focusRing,
            styles.segment,
            compact && styles.segmentCompact,
            option.value === value && styles.segmentOn,
          )}
        >
          {option.label}
        </ToggleGroup.Item>
      ))}
    </ToggleGroup.Root>
  );
}

/** A choice from a longer list: a field-like trigger opening a menu of radio items. */
export function MenuSelect({
  label,
  options,
  value,
  onChange,
}: {
  label: string;
  options: Option[];
  value: string | undefined;
  onChange: (value: string) => void;
}) {
  const current = options.find((option) => option.value === value);
  return (
    <Menu.Root modal={false}>
      <Menu.Trigger asChild>
        <button
          type="button"
          aria-label={`${label}: ${current?.label ?? "None"}`}
          {...stylex.props(ui.reset, ui.focusRing, styles.selectTrigger)}
        >
          <span {...stylex.props(ui.ellipsis)}>{current?.label ?? "Choose"}</span>
          <ChevronDown aria-hidden="true" {...stylex.props(ui.iconSmall, ui.tertiary)} />
        </button>
      </Menu.Trigger>
      <Menu.Portal>
        <Menu.Content
          align="start"
          sideOffset={parseFloat(space.x1)}
          collisionPadding={parseFloat(space.x2)}
          {...stylex.props(ui.menu)}
        >
          <Menu.RadioGroup value={value ?? ""} onValueChange={onChange}>
            {options.map((option) => (
              <Menu.RadioItem
                key={option.value}
                value={option.value}
                {...stylex.props(ui.menuItem)}
              >
                <span {...stylex.props(ui.ellipsis)}>{option.label}</span>
                <Menu.ItemIndicator {...stylex.props(styles.check)}>
                  <Check aria-hidden="true" {...stylex.props(ui.iconSmall)} />
                </Menu.ItemIndicator>
              </Menu.RadioItem>
            ))}
          </Menu.RadioGroup>
        </Menu.Content>
      </Menu.Portal>
    </Menu.Root>
  );
}

/** A checkbox row: the box, the label, an optional trailing note. */
export function CheckRow({
  checked,
  onChange,
  label,
  trail,
}: {
  checked: boolean;
  onChange: (checked: boolean) => void;
  label: string;
  trail?: string;
}) {
  return (
    <label {...stylex.props(styles.checkRow)}>
      <Checkbox.Root
        checked={checked}
        onCheckedChange={(next) => onChange(next === true)}
        {...stylex.props(ui.reset, ui.focusRing, styles.checkbox)}
      >
        <span {...stylex.props(styles.checkboxBox, checked && styles.checkboxOn)}>
          <Checkbox.Indicator {...stylex.props(styles.checkboxMark)}>
            <Check
              aria-hidden="true"
              strokeWidth={stroke.checkMark}
              {...stylex.props(ui.iconSmall)}
            />
          </Checkbox.Indicator>
        </span>
      </Checkbox.Root>
      <span {...stylex.props(ui.ellipsis, styles.checkLabel)}>{label}</span>
      {trail ? <span {...stylex.props(ui.small, ui.tertiary)}>{trail}</span> : null}
    </label>
  );
}

/** A single-line text field (16px, so iOS does not zoom). */
export const TextField = forwardRef<
  HTMLInputElement,
  JSX.IntrinsicElements["input"] & { mono?: boolean }
>(function TextField({ mono = false, ...rest }, ref) {
  return <input {...rest} ref={ref} {...stylex.props(styles.field, mono && ui.mono)} />;
});

/** A labelled control in Settings: the label, the control, a note under it. */
export function Labelled({
  label,
  note,
  children,
}: {
  label: string;
  note?: string;
  children: ComponentChildren;
}) {
  return (
    <div {...stylex.props(styles.labelled)}>
      <span {...stylex.props(styles.label)}>{label}</span>
      {children}
      {note ? <p {...stylex.props(ui.small, ui.tertiary)}>{note}</p> : null}
    </div>
  );
}

/** One line reporting the result of an action; errors in full ink. */
export function Status({ text, error = false }: { text: string; error?: boolean }) {
  return (
    <p role="status" {...stylex.props(ui.small, error ? styles.statusError : ui.secondary)}>
      {text}
    </p>
  );
}

const styles = stylex.create({
  iconButton: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    flexShrink: 0,
    width: { default: size.row, [media.touch]: size.touch },
    height: { default: size.row, [media.touch]: size.touch },
    borderRadius: radius.control,
    color: { default: colors.secondary, ":hover": { [media.hover]: colors.primary } },
    backgroundColor: {
      default: "transparent",
      ":hover": { [media.hover]: colors.hover },
      ":active": colors.hover,
    },
  },
  tooltip: {
    zIndex: layer.tooltip,
    display: "flex",
    alignItems: "center",
    columnGap: space.x2,
    paddingBlock: space.x1,
    paddingInline: space.x2,
    borderRadius: radius.control,
    backgroundColor: colors.primary,
    color: colors.bg,
    fontSize: type.small,
    lineHeight: type.smallLine,
    fontWeight: weight.medium,
    userSelect: "none",
  },
  tooltipKeys: { opacity: opacity.dim, fontWeight: weight.regular },
  textButton: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    minHeight: { default: size.control, [media.touch]: size.touch },
    minWidth: { default: null, [media.touch]: size.touch },
    paddingInline: space.x1,
    marginInline: `calc(-1 * ${space.x1})`,
    borderRadius: radius.control,
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: { default: colors.secondary, ":hover": { [media.hover]: colors.primary } },
  },
  textStrong: { color: colors.primary, fontWeight: weight.medium },
  button: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    columnGap: space.x2,
    flexShrink: 0,
    height: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x4,
    borderRadius: radius.control,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: colors.hairline,
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
    color: colors.primary,
    fontWeight: weight.medium,
    whiteSpace: "nowrap",
    opacity: { default: 1, ":disabled": opacity.disabled },
    cursor: { default: "pointer", ":disabled": "default" },
  },
  primary: {
    borderColor: colors.primary,
    backgroundColor: { default: colors.primary, ":hover": { [media.hover]: colors.secondary } },
    color: colors.bg,
  },
  danger: {
    borderColor: colors.danger,
    backgroundColor: { default: colors.danger, ":hover": { [media.hover]: colors.danger } },
    color: colors.bg,
  },
  track: {
    display: "inline-flex",
    maxWidth: "100%",
    padding: { default: space.x1, [media.touch]: 0 },
    borderRadius: radius.control,
    backgroundColor: colors.surface,
    overflowX: "auto",
  },
  trackCompact: { padding: { default: space.x05, [media.touch]: 0 } },
  segment: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    flexShrink: 0,
    height: { default: size.control, [media.touch]: size.touch },
    minWidth: { default: null, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: { default: radius.code, [media.touch]: radius.control },
    fontSize: type.small,
    lineHeight: type.smallLine,
    whiteSpace: "nowrap",
    color: { default: colors.secondary, ":hover": { [media.hover]: colors.primary } },
    backgroundColor: "transparent",
  },
  segmentOn: {
    color: colors.primary,
    fontWeight: weight.medium,
    backgroundColor: colors.bg,
    boxShadow: `inset 0 0 0 ${stroke.hairline} ${colors.hairline}`,
  },
  segmentCompact: { paddingInline: space.x2 },
  selectTrigger: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "space-between",
    columnGap: space.x2,
    minWidth: size.select,
    maxWidth: "100%",
    height: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: radius.control,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: colors.hairline,
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
  },
  check: { display: "flex", marginInlineStart: "auto", paddingInlineStart: space.x3 },
  checkRow: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x3,
    minHeight: { default: size.row, [media.touch]: size.touch },
    cursor: "pointer",
  },
  checkbox: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    flexShrink: 0,
    width: { default: size.control, [media.touch]: size.touch },
    height: { default: size.control, [media.touch]: size.touch },
    marginInline: { default: `-${space.x1}`, [media.touch]: `-${space.x3}` },
    borderRadius: radius.control,
  },
  checkboxBox: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    width: size.checkbox,
    height: size.checkbox,
    borderRadius: radius.code,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: colors.tertiary,
    color: colors.bg,
  },
  checkboxOn: { borderColor: colors.primary, backgroundColor: colors.primary },
  checkboxMark: { display: "flex" },
  checkLabel: { flexGrow: 1 },
  field: {
    boxSizing: "border-box",
    width: "100%",
    minWidth: 0,
    height: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: radius.control,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: { default: colors.hairline, ":focus": colors.tertiary },
    backgroundColor: "transparent",
    color: colors.primary,
    fontSize: type.text,
    outline: "none",
    "::placeholder": { color: colors.tertiary },
  },
  labelled: {
    display: "flex",
    flexDirection: "column",
    alignItems: "flex-start",
    rowGap: space.x2,
  },
  label: { fontWeight: weight.medium },
  statusError: { color: colors.danger },
});
