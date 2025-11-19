import { forwardRef, ButtonHTMLAttributes } from "react";

interface ButtonProps extends ButtonHTMLAttributes<HTMLButtonElement> {
  variant?: "primary" | "secondary" | "danger";
}

export const Button = forwardRef<HTMLButtonElement, ButtonProps>(
  (
    { children, className = "", variant = "secondary", disabled, ...props },
    ref,
  ) => {
    const baseStyles =
      "px-3 py-2 text-sm rounded-md font-medium transition-all duration-150 active:scale-95 focus:outline-none focus:ring-2 focus:ring-offset-2";

    const variantStyles = {
      primary:
        "bg-blue-600 hover:bg-blue-700 active:bg-blue-800 text-white focus:ring-blue-500 disabled:bg-gray-300 disabled:text-gray-500",
      secondary:
        "bg-gray-600 hover:bg-gray-700 active:bg-gray-800 text-white focus:ring-gray-500 disabled:bg-gray-300 disabled:text-gray-500",
      danger:
        "bg-red-600 hover:bg-red-700 active:bg-red-800 text-white focus:ring-red-500 disabled:bg-gray-300 disabled:text-gray-500",
    };

    const disabledStyles = disabled ? "cursor-not-allowed" : "cursor-pointer";

    return (
      <button
        ref={ref}
        className={`${baseStyles} ${variantStyles[variant]} ${disabledStyles} ${className}`}
        disabled={disabled}
        {...props}
      >
        {children}
      </button>
    );
  },
);

Button.displayName = "Button";
