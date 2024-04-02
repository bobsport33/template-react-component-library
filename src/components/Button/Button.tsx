import React from "react";
// import "./Button.css";
import { styled } from "@mui/material";

interface ButtonProps {
    label: string;
}

const ButtonWrapper = styled("button")`
    font-size: 5rem;
    background-color: aquamarine;
    border: none;
`;

const Button = (props: ButtonProps) => {
    return <ButtonWrapper>{props.label}</ButtonWrapper>;
};

export default Button;
