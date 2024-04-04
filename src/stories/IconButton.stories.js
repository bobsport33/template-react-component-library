import React from "react";
import IconButton from "../components/IconButton/IconButton";

import { BackupTable, TableChart } from "@mui/icons-material";
import InfoIcon from "@mui/icons-material/Info";
import ZoomOutMapIcon from "@mui/icons-material/ZoomOutMap";

export default {
    title: "components/Icon Button",
    component: IconButton,
};

export const HelpText = {
    args: {
        icon: <InfoIcon />,
    },
};

export const DetailedData = {
    args: {
        icon: <BackupTable />,
    },
};

export const ChangeView = {
    args: {
        icon: <TableChart />,
    },
};
export const MaxView = {
    args: {
        icon: <ZoomOutMapIcon />,
    },
};
