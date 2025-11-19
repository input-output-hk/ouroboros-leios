import { FC, ButtonHTMLAttributes } from "react";

interface ButtonProps extends ButtonHTMLAttributes<HTMLButtonElement> {
  variant?: "primary" | "secondary" | "danger";
  size?: "sm" | "md";
}

export const Button: FC<ButtonProps> = ({
  children,
  className = "",
  variant = "secondary",
  size = "md",
  disabled,
  ...props
}) => {
  const baseStyles = "rounded-md font-medium transition-all duration-150 active:scale-95 focus:outline-none focus:ring-2 focus:ring-offset-2";
  
  const variantStyles = {
    primary: "bg-blue-600 hover:bg-blue-700 active:bg-blue-800 text-white focus:ring-blue-500 disabled:bg-gray-300 disabled:text-gray-500",
    secondary: "bg-gray-600 hover:bg-gray-700 active:bg-gray-800 text-white focus:ring-gray-500 disabled:bg-gray-300 disabled:text-gray-500", 
    danger: "bg-red-600 hover:bg-red-700 active:bg-red-800 text-white focus:ring-red-500 disabled:bg-gray-300 disabled:text-gray-500"
  };
  
  const sizeStyles = {
    sm: "px-2 py-1 text-sm",
    md: "px-4 py-2 text-sm"
  };
  
  const disabledStyles = disabled ? "cursor-not-allowed" : "cursor-pointer";
  
  return (
    <button
      className={`${baseStyles} ${variantStyles[variant]} ${sizeStyles[size]} ${disabledStyles} ${className}`}
      disabled={disabled}
      {...props}
    >
      {children}
    </button>
  );
};