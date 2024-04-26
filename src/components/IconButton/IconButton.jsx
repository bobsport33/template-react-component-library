import React from "react";
import { styled } from "@mui/material";
import PropTypes from "prop-types";

const IconButtonWrapper = styled("button")`
    height: 36px;
    width: 30px !important;
    max-width: 30px !important;
    min-width: 30px !important;
    background-color: #f4f4f4 !important;
    color: #333 !important;
    /* border-radius: 20px; */
    display: inline-flex;
    -webkit-box-align: center;
    align-items: center;
    -webkit-box-pack: center;
    justify-content: center;
    position: relative;
    box-sizing: border-box;
    -webkit-tap-highlight-color: transparent;
    outline: 0px;
    border: 0px;
    margin: 0px;
    cursor: pointer;
    user-select: none;
    vertical-align: middle;
    appearance: none;
    text-decoration: none;
    font-family: Roboto, Helvetica, Arial, sans-serif;
    font-weight: 500;
    font-size: 0.875rem;
    line-height: 1.75;
    letter-spacing: 0.02857em;
    text-transform: uppercase;
    padding: 6px 16px;
    transition:
        background-color 250ms cubic-bezier(0.4, 0, 0.2, 1) 0ms,
        box-shadow 250ms cubic-bezier(0.4, 0, 0.2, 1) 0ms,
        border-color 250ms cubic-bezier(0.4, 0, 0.2, 1) 0ms,
        color 250ms cubic-bezier(0.4, 0, 0.2, 1) 0ms;
    color: rgb(255, 255, 255);
    background-color: rgb(25, 118, 210);
    box-shadow:
        rgba(0, 0, 0, 0.2) 0px 3px 1px -2px,
        rgba(0, 0, 0, 0.14) 0px 2px 2px 0px,
        rgba(0, 0, 0, 0.12) 0px 1px 5px 0px;
`;

const IconButton = ({ icon, onClick, round }) => {
    return (
        <IconButtonWrapper
            onClick={onClick}
            style={{ borderRadius: round ? "20px" : "4px" }}
        >
            {icon}
        </IconButtonWrapper>
    );
};

IconButton.propTypes = {
    icon: PropTypes.element,
    onClick: PropTypes.func,
};

export default IconButton;
