import { useEffect, useState } from "react";
import { TextButton } from "./controls.tsx";

/** "Copy", then "Copied" for a moment (or "Not copied" when the clipboard refuses). */
export function CopyButton({
  text,
  label = "Copy",
}: {
  text: string | (() => string);
  label?: string;
}) {
  const [state, setState] = useState<"idle" | "done" | "failed">("idle");
  useEffect(() => {
    if (state === "idle") return undefined;
    const timer = setTimeout(() => setState("idle"), 1500);
    return () => clearTimeout(timer);
  }, [state]);
  return (
    <TextButton
      aria-live="polite"
      onClick={() => {
        navigator.clipboard.writeText(typeof text === "function" ? text() : text).then(
          () => setState("done"),
          () => setState("failed"),
        );
      }}
    >
      {state === "done" ? "Copied" : state === "failed" ? "Not copied" : label}
    </TextButton>
  );
}
