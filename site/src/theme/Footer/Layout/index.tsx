import { useThemeConfig } from "@docusaurus/theme-common";
import {
  DiscordIcon,
  FacebookIcon,
  GitHubIcon,
  LinkedInIcon,
  TwitterIcon,
} from "@site/src/components/icons";
import type { Props } from "@theme/Footer/Layout";
import clsx from "clsx";
import { JSX } from "react";

export default function FooterLayout({
  style,
  links,
  logo,
  copyright,
}: Props): JSX.Element {
  const config = useThemeConfig();
  const { socials, legal } = config as {
    socials?: {
      tagline: string;
      items: {
        platform: string;
        url: string;
      }[];
    };
    legal?: {
      label: string;
      to: string;
    }[];
  };

  const socialIcons: Record<string, JSX.Element> = {
    github: <GitHubIcon />,
    discord: <DiscordIcon />,
    twitter: <TwitterIcon />,
    linkedin: <LinkedInIcon />,
    facebook: <FacebookIcon />,
  };

  return (
    <footer
      className={clsx("footer", {
        "footer--dark": style === "dark",
      })}
    >
      <div className="container">
        <div className="container-padding">
          <div className="footer-content">
            <div className="footer-socials">
              <h4 className="footer-socials-tagline">{socials.tagline}</h4>
              <div className="footer-socials-separator" />
              <div className="footer-socials-items">
                {socials.items.map((item) => (
                  <a
                    key={item.platform}
                    href={item.url}
                    target="_blank"
                    rel="noopener noreferrer"
                    className="footer-socials-item"
                  >
                    {socialIcons[item.platform.toLowerCase()] ?? <GitHubIcon />}
                  </a>
                ))}
              </div>
            </div>
            {links}
            {(logo || copyright) && (
              <div className="footer__bottom">
                {logo && logo}
                <div className="footer__bottom_legal">
                  {legal.map((item) => (
                    <a
                      key={item.label}
                      href={item.to}
                      target="_blank"
                      rel="noopener noreferrer"
                      className="footer__link-item"
                    >
                      {item.label}
                    </a>
                  ))}
                </div>
              </div>
            )}
          </div>
        </div>
      </div>
    </footer>
  );
}
