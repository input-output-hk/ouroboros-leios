import { createTheme } from "@mui/material/styles";

export const theme = createTheme({
  palette: {
    mode: "dark",
    primary: { main: "#90caf9" },
    secondary: { main: "#f48fb1" },
    background: {
      default: "#121212",
      paper: "#1e1e1e",
    },
  },
  typography: {
    fontFamily: '"Roboto Mono", "Roboto", monospace',
    fontSize: 13,
  },
});
