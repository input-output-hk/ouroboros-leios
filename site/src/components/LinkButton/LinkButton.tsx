import { ArrowRightIcon, FileIcon } from "../icons";
import styles from "./styles.module.css";

type LinkButton = {
  text: string;
  url: string;
  target?: string;
  rel?: string;
};

export function LinkButton({ text, url, target, rel }: LinkButton) {
  return (
    <a href={url} className={styles.linkButton} target={target} rel={rel}>
      <span>
        <FileIcon />
        {text}
      </span>
      <ArrowRightIcon />
    </a>
  );
}
